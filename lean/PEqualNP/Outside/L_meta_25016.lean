import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25016

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem wiresFrom_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresFrom (gs ++ [g]) x = wiresFrom gs x ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs x).getD i false)] := by
  rw [wiresFrom_append]; rfl

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def reads (g : Gate) : List ℕ := match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def credit (g : Gate) : ℕ := match g.op with
  | .not => 0
  | _ => 1

def credits (gs : List Gate) : ℕ := (gs.map credit).sum

theorem reads_length (g : Gate) (h : g.inputs.length ≤ 2) :
    (reads g).length ≤ 1 + credit g := by
  cases g with
  | mk op inputs =>
    cases op <;> simp [reads, credit, List.length_take] at h ⊢ <;> omega

theorem eval_reads (g : Gate) (x : ℕ → Bool) :
    g.op.eval (g.inputs.map x) = g.op.eval ((reads g).map x) := by
  cases g with
  | mk op inputs =>
    cases op <;> try rfl
    cases inputs <;> rfl

theorem credits_le (gs : List Gate) : credits gs ≤ gs.length := by
  induction gs with
  | nil => simp [credits]
  | cons g gs ih =>
    have hg : credit g ≤ 1 := by rcases g with ⟨op, inputs⟩; cases op <;> simp [credit]
    simp only [credits, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

theorem credits_of_not (gs : List Gate) (g : Gate) (h : g ∈ gs) (hn : g.op = .not) :
    credits gs + 1 ≤ gs.length := by
  obtain ⟨p, q, rfl⟩ := List.append_of_mem h
  have hp := credits_le p
  have hq := credits_le q
  have hz : credit g = 0 := by simp [credit, hn]
  simp only [credits, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    List.length_append, List.length_cons, hz] at hp hq ⊢
  omega

theorem credits_snoc (gs : List Gate) (g : Gate) :
    credits (gs ++ [g]) = credits gs + credit g := by
  simp [credits]

theorem needed (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ N : Finset ℕ, ∃ N' : Finset ℕ, N'.card ≤ N.card + credits gs ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ N', x.getD i false = y.getD i false) →
        ∀ i ∈ N, (wiresFrom gs x).getD i false = (wiresFrom gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => intro N; exact ⟨N, by simp, fun x y _ _ h => h⟩
  | append_singleton gs g ih =>
    intro N
    have hgs : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g' h => hg g' (List.mem_append_left _ h)
    have hg2 := reads_length g (hg g (by simp))
    by_cases hm : n + gs.length ∈ N
    · obtain ⟨N', hc, hN⟩ := ih hgs (N.erase (n + gs.length) ∪ (reads g).toFinset)
      refine ⟨N', ?_, fun x y hx hy h i hi => ?_⟩
      · have h1 := Finset.card_union_le (N.erase (n + gs.length)) (reads g).toFinset
        have h2 := Finset.card_erase_of_mem hm
        have h3 := List.toFinset_card_le (reads g)
        have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, hm⟩
        rw [credits_snoc]
        omega
      · have H := hN x y hx hy h
        rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom,
          length_wiresFrom, hx, hy]
        split_ifs with hk
        · rw [eval_reads g, eval_reads g]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact H a (Finset.mem_union_right _ (List.mem_toFinset.2 ha))
        · exact H i (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hk, hi⟩))
    · obtain ⟨N', hc, hN⟩ := ih hgs N
      refine ⟨N', ?_, fun x y hx hy h i hi => ?_⟩
      · rw [credits_snoc]; omega
      · rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom,
          length_wiresFrom, hx, hy]
        have hk : i ≠ n + gs.length := fun h => hm (h ▸ hi)
        rw [ite_eq_right hk, ite_eq_right hk]
        exact hN x y hx hy h i hi

def inp (N : ℕ) (P : Finset ℕ) : List Bool := List.ofFn fun i : Fin N => decide ((i : ℕ) ∈ P)

theorem inp_getD (N : ℕ) (P : Finset ℕ) (i : ℕ) :
    (inp N P).getD i false = decide (i < N ∧ i ∈ P) := by
  unfold inp
  by_cases h : i < N <;> simp [List.getD_eq_getElem?_getD, h]

theorem oneEach_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    oneEach u v = inp (n + m) {(u : ℕ), n + (v : ℕ)} := by
  have hu := u.2
  have hv := v.2
  apply List.ext_getElem
  · simp [oneEach, inp]
  · intro i h1 h2
    simp only [oneEach, inp, List.length_append, List.length_ofFn] at h1 h2 ⊢
    by_cases hi : i < n
    · rw [List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_ofFn, Fin.ext_iff, Finset.mem_insert, Finset.mem_singleton,
        decide_eq_decide]
      omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff, Finset.mem_insert,
        Finset.mem_singleton, decide_eq_decide]
      omega

theorem support_bound {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (left : ∀ u u', (∀ v, A u v = A u' v) → u = u')
    (right : ∀ v v', (∀ u, A u v = A u v') → v = v')
    (hc : FanInTwo C) (rep : Represents A C) :
    n + m ≤ credits C.gates + 3 := by
  classical
  obtain ⟨D, hcard, support⟩ := needed (n+m) C.gates (fun g hg => (hc g hg).2) {C.output}
  simp only [Finset.card_singleton] at hcard
  have agree (u u' : Fin n) (v v' : Fin m)
      (h : ∀ i ∈ D, (i = u ∨ i = n + v.val) ↔ (i = u' ∨ i = n + v'.val)) :
      A u v = A u' v' := by
    rw [←rep u v, ←rep u' v', oneEach_eq, oneEach_eq]
    apply support _ _ (by simp [inp]) (by simp [inp]) _ C.output (by simp)
    intro i hi
    simpa only [inp_getD, decide_eq_decide, Finset.mem_insert, Finset.mem_singleton] using
      and_congr_right (fun _ : i < n+m => h i hi)
  let L := Finset.range n
  let R := (Finset.range m).image (fun j => n+j)
  have lsize : L.card = n := Finset.card_range _
  have rsize : R.card = m := by
    dsimp [R]
    rw [Finset.card_image_of_injective _ (fun a b e => by simpa using e), Finset.card_range]
  have missL : (L \ D).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha,na⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨hb,nb⟩ := Finset.mem_sdiff.mp hb
    have e := left ⟨a,Finset.mem_range.mp ha⟩ ⟨b,Finset.mem_range.mp hb⟩ (fun v => by
      apply agree
      intro i hi
      have ea : i ≠ a := fun e => na (e ▸ hi)
      have eb : i ≠ b := fun e => nb (e ▸ hi)
      simp [ea,eb])
    exact congrArg Fin.val e
  have missR : (R \ D).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hx,nx⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hy,ny⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    have e := right ⟨a,Finset.mem_range.mp ha⟩ ⟨b,Finset.mem_range.mp hb⟩ (fun u => by
      apply agree
      intro i hi
      have ea : i ≠ n+a := fun e => nx (e ▸ hi)
      have eb : i ≠ n+b := fun e => ny (e ▸ hi)
      simp [ea,eb])
    exact congrArg (fun v : Fin m => n + v.val) e
  have dis : Disjoint (L ∩ D) (R ∩ D) := by
    apply Finset.disjoint_left.mpr
    intro i hi hr
    have lt := Finset.mem_range.mp (Finset.mem_inter.mp hi).1
    obtain ⟨j,_,eq⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hr).1
    omega
  have sub : (L ∩ D) ∪ (R ∩ D) ⊆ D := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h <;> exact (Finset.mem_inter.mp h).2
  have count := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dis] at count
  have lc := Finset.card_sdiff_add_card_inter L D
  have rc := Finset.card_sdiff_add_card_inter R D
  omega

end PEqualNP.Outside.L_meta_25016

theorem PEqualNP.Outside.L_meta_25016 : (∀ (n m : ℕ) (A : Fin n → Fin m → Bool), 2 ≤ n → 2 ≤ m → (∀ u u' : Fin n, (∀ v : Fin m, A u v = A u' v) → u = u') → (∀ v v' : Fin m, (∀ u : Fin n, A u v = A u v') → v = v') → ¬ PEqualNP.Represents.RepSizeAtMost A (n + m - 3) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → n + m - 2 ≤ C.size) := by
  intro n m A hn hm rows cols lower C hc rep
  by_contra! small
  have bound := PEqualNP.Outside.L_meta_25016.support_bound rows cols hc rep
  have hlen : C.gates.length < n+m-2 := small
  have noNot (g) (hg : g ∈ C.gates) : g.op ≠ .not := by
    intro eq
    have := PEqualNP.Outside.L_meta_25016.credits_of_not C.gates g hg eq
    omega
  apply lower
  refine ⟨C, ?_, by omega, rep⟩
  intro g hg
  refine ⟨?_, (hc g hg).2⟩
  have op := (hc g hg).1
  have nn := noNot g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
  tauto
