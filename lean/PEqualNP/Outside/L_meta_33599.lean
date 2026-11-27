import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33599

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Represents

-- Credit: wiresFrom lemmas and reads_le below are copied from PEqualNP.MetaComplexity.Helpers
-- (Shannon and RepReads), inlined because those modules are not built here.


/-- Run gates on a wire list: the fold inside `Circuit.wires`. -/
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

/-- The wires that decide a set `N` of wires: at most one more per gate. -/
theorem needed (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ N : Finset ℕ, ∃ N' : Finset ℕ, N'.card ≤ N.card + gs.length ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ N', x.getD i false = y.getD i false) →
        ∀ i ∈ N, (wiresFrom gs x).getD i false = (wiresFrom gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => intro N; exact ⟨N, by simp, fun x y _ _ h => h⟩
  | append_singleton gs g ih =>
    intro N
    have hgs : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g' h => hg g' (List.mem_append_left _ h)
    have hg2 : g.inputs.length ≤ 2 := hg g (by simp)
    by_cases hm : n + gs.length ∈ N
    · obtain ⟨N', hc, hN⟩ := ih hgs (N.erase (n + gs.length) ∪ g.inputs.toFinset)
      refine ⟨N', ?_, fun x y hx hy h i hi => ?_⟩
      · have h1 := Finset.card_union_le (N.erase (n + gs.length)) g.inputs.toFinset
        have h2 := Finset.card_erase_of_mem hm
        have h3 := List.toFinset_card_le g.inputs
        have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, hm⟩
        rw [List.length_append, List.length_singleton]
        omega
      · have H := hN x y hx hy h
        rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom,
          length_wiresFrom, hx, hy]
        split_ifs with hk
        · congr 1
          apply List.map_congr_left
          intro a ha
          exact H a (Finset.mem_union_right _ (List.mem_toFinset.2 ha))
        · exact H i (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hk, hi⟩))
    · obtain ⟨N', hc, hN⟩ := ih hgs N
      refine ⟨N', ?_, fun x y hx hy h i hi => ?_⟩
      · rw [List.length_append, List.length_singleton]; omega
      · rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom,
          length_wiresFrom, hx, hy]
        have hk : i ≠ n + gs.length := fun h => hm (h ▸ hi)
        rw [if_neg hk, if_neg hk]
        exact hN x y hx hy h i hi

/-- AND and OR gates are monotone. -/
theorem op_mono (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (S T : ℕ → Bool) (h : ∀ i, S i = true → T i = true)
    (he : g.op.eval (g.inputs.map S) = true) : g.op.eval (g.inputs.map T) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> rw [hop] at he ⊢
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at he ⊢
    exact fun i hi => h i (he i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at he ⊢
    obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hv⟩

theorem mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (wiresFrom gs x).getD i false = true → (wiresFrom gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => exact h
  | append_singleton gs g ih =>
    have H := ih fun g' h' => hg g' (List.mem_append_left _ h')
    intro i
    rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom, length_wiresFrom,
      hl]
    split_ifs with hk
    · exact op_mono g (hg g (by simp)) _ _ H
    · exact H i

/-- The input with the vertices of `P` on (wires). -/
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

/-- The left vertices that must be read. -/
def forcedL {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun u => ∃ v, A u v = true ∧ ∃ u', A u' v = false

/-- The right vertices that must be read. -/
def forcedR {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun v => ∃ u, A u v = true ∧ ∃ w, A u w = false

/-- The vertices that must be read number at most the size plus one. -/
theorem reads_le {n m s : ℕ} (A : Fin n → Fin m → Bool) (h : RepSizeAtMost A s) :
    (forcedL A).card + (forcedR A).card ≤ s + 1 := by
  obtain ⟨C, hC, hs, hR⟩ := h
  obtain ⟨S, hcard, hS⟩ := needed (n + m) C.gates (fun g hg => (hC g hg).2) {C.output}
  have hop : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
    fun g hg => (hC g hg).1
  have hev : ∀ P, C.eval (inp (n + m) P) =
      (wiresFrom C.gates (inp (n + m) P)).getD C.output false := fun P => rfl
  -- turning off an unread wire changes nothing
  have hoff : ∀ P w, w ∉ S → C.eval (inp (n + m) P) = C.eval (inp (n + m) (P.erase w)) := by
    intro P w hw
    rw [hev, hev]
    refine hS _ _ (by simp [inp]) (by simp [inp]) (fun i hi => ?_) _ (Finset.mem_singleton_self _)
    rw [inp_getD, inp_getD, decide_eq_decide, Finset.mem_erase]
    have : i ≠ w := fun e => hw (e ▸ hi)
    tauto
  have hmono : ∀ P Q : Finset ℕ, P ⊆ Q → C.eval (inp (n + m) P) = true →
      C.eval (inp (n + m) Q) = true := by
    intro P Q hPQ
    rw [hev, hev]
    refine mono C.gates hop _ _ (by simp [inp]) (fun i => ?_) _
    rw [inp_getD, inp_getD, decide_eq_true_eq, decide_eq_true_eq]
    exact fun ⟨a, b⟩ => ⟨a, hPQ b⟩
  have hA : ∀ (u : Fin n) (v : Fin m), C.eval (inp (n + m) {(u : ℕ), n + (v : ℕ)}) = A u v := by
    intro u v
    rw [← oneEach_eq]; exact hR u v
  have hL : ∀ u ∈ forcedL A, (u : ℕ) ∈ S := by
    intro u hu
    obtain ⟨v, h1, u', h2⟩ := (Finset.mem_filter.1 hu).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} u hw
    rw [hA, h1] at e
    have := hmono _ {(u' : ℕ), n + (v : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hRr : ∀ v ∈ forcedR A, n + (v : ℕ) ∈ S := by
    intro v hv
    obtain ⟨u, h1, w, h2⟩ := (Finset.mem_filter.1 hv).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} (n + v) hw
    rw [hA, h1] at e
    have := hmono _ {(u : ℕ), n + (w : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hsub : (forcedL A).image (fun u : Fin n => (u : ℕ)) ∪
      (forcedR A).image (fun v : Fin m => n + (v : ℕ)) ⊆ S := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hi; exact hL u hu
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi; exact hRr v hv
  have hdis : Disjoint ((forcedL A).image (fun u : Fin n => (u : ℕ)))
      ((forcedR A).image (fun v : Fin m => n + (v : ℕ))) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨v, _, hv⟩ := Finset.mem_image.1 h2
    have := u.2
    omega
  have hcc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))] at hcc
  rw [Finset.card_singleton] at hcard
  have : C.gates.length ≤ s := hs
  omega


/-- A gate with its inputs renamed by `r`. -/
def rg (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

theorem getD_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

/-- Renaming wires: the copied gates read the renamed wires and agree with the old ones. -/
theorem ren (x y : List Bool) (d : ℕ) (r : ℕ → ℕ) (hy : y.length = x.length + d)
    (hr : ∀ w, x.length ≤ w → r w = w + d) (hlt : ∀ w, w < x.length → r w < y.length)
    (hv : ∀ w, w < x.length → y.getD (r w) false = x.getD w false) (gs : List Gate) :
    ∀ w, (wiresFrom (gs.map (rg r)) y).getD (r w) false = (wiresFrom gs x).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    by_cases h : w < x.length
    · exact hv w h
    · have := hr w (by omega)
      simp only [List.map_nil]
      show y.getD (r w) false = x.getD w false
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | append_singleton gs g ih =>
    intro w
    rw [List.map_append, List.map_singleton, wiresFrom_snoc, wiresFrom_snoc, getD_snoc,
      getD_snoc, length_wiresFrom, length_wiresFrom, List.length_map]
    by_cases hw : w = x.length + gs.length
    · have := hr w (by omega)
      rw [if_pos (by omega), if_pos hw]
      simp only [rg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact ih a
    · have : r w ≠ y.length + gs.length := by
        by_cases h : w < x.length
        · have := hlt w h; omega
        · have := hr w (by omega); omega
      rw [if_neg this, if_neg hw]
      exact ih w

/-- The guard wire after `k` OR gates. -/
def acc (N k : ℕ) : ℕ := if k = 0 then 0 else N + k - 1

/-- The OR chain over wires `0` to `k`. -/
def chain (N : ℕ) : ℕ → List Gate
  | 0 => []
  | k + 1 => chain N k ++ [⟨GateOp.or, [acc N k, k + 1]⟩]

theorem chain_length (N k : ℕ) : (chain N k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [chain, ih]

theorem chain_gates (N k : ℕ) : ∀ g ∈ chain N k, g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction k with
  | zero => intro g hg; simp [chain] at hg
  | succ k ih =>
    intro g hg
    simp only [chain, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact ih g hg
    · subst hg; exact ⟨rfl, rfl⟩

theorem chain_val (N a : ℕ) (x : List Bool) (hx : x.length = N) :
    ∀ k, k < N → (∀ i, i ≤ k → x.getD i false = decide (i = a)) →
      (wiresFrom (chain N k) x).getD (acc N k) false = decide (a ≤ k) := by
  intro k
  induction k with
  | zero =>
    intro hk h
    simp only [chain, acc, if_pos]
    show x.getD 0 false = _
    rw [h 0 (le_refl 0)]
    simp only [decide_eq_decide]; omega
  | succ k ih =>
    intro hk h
    have H := ih (by omega) (fun i hi => h i (by omega))
    simp only [chain]
    rw [wiresFrom_snoc, getD_snoc, length_wiresFrom, chain_length, hx]
    have hacc : acc N (k + 1) = N + k := by simp [acc]
    rw [hacc, if_pos rfl]
    have h2 : (wiresFrom (chain N k) x).getD (k + 1) false = decide (k + 1 = a) := by
      rw [getD_prefix _ _ _ (by omega), h (k + 1) (le_refl _)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
      Bool.or_false, H, h2]
    by_cases h3 : a ≤ k
    · simp [h3]; omega
    · by_cases h4 : k + 1 = a
      · simp [h4]
      · simp [h3, h4]; omega

theorem part1 (n m s : ℕ) (A : Fin n → Fin m → Bool) (hA : RepSizeAtMost A s) :
    RepSizeAtMost
      (fun (i : Fin (n+1)) j => if h : i.val < n then A ⟨i.val,h⟩ j else false) (s+n) := by
  obtain ⟨C, hC, hs, hR⟩ := hA
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨⟨[], 1 + m⟩, fun g hg => by simp at hg, by simp [Circuit.size], fun u v => ?_⟩
    have : ¬ u.val < 0 := by omega
    show (oneEach u v).getD (1 + m) false = (if h : u.val < 0 then A ⟨u.val, h⟩ v else false)
    rw [dif_neg this, List.getD_eq_default _ _ (by simp [oneEach])]
  · let N := n + 1 + m
    let r : ℕ → ℕ := fun w => if w < n then w else if w < n + m then w + 1 else w + n
    let G : List Gate := chain N (n - 1) ++ C.gates.map (rg r) ++
      [⟨GateOp.and, [r C.output, acc N (n - 1)]⟩]
    refine ⟨⟨G, N + (n - 1) + C.gates.length⟩, ?_, ?_, ?_⟩
    · intro g hg
      simp only [G, List.mem_append, List.mem_singleton, List.mem_map] at hg
      rcases hg with (hg | ⟨g', hg', rfl⟩) | rfl
      · obtain ⟨h1, h2⟩ := chain_gates N (n - 1) g hg
        exact ⟨by rw [h1]; simp, by omega⟩
      · exact ⟨(hC g' hg').1, by simp only [rg, List.length_map]; exact (hC g' hg').2⟩
      · exact ⟨by simp, by simp⟩
    · show G.length ≤ s + n
      have : C.gates.length ≤ s := hs
      simp only [G, List.length_append, chain_length, List.length_map, List.length_singleton]
      omega
    · intro u v
      have hu := u.2
      have hvv := v.2
      let x' := oneEach u v
      have hx'l : x'.length = N := by simp [x', oneEach, N]; omega
      have hx' : ∀ i, x'.getD i false = decide (i < N ∧ (i = u.val ∨ i = n + 1 + v.val)) := by
        intro i
        simp only [x']
        rw [oneEach_eq, inp_getD]
        simp [N]
      let P : Finset ℕ := (Finset.range (n + m)).filter
        (fun w => r w = u.val ∨ r w = n + 1 + v.val)
      let x := inp (n + m) P
      have hxl : x.length = n + m := by simp [x, inp]
      let Y := wiresFrom (chain N (n - 1)) x'
      have hYl : Y.length = x.length + n := by
        simp only [Y]
        rw [length_wiresFrom, chain_length, hx'l, hxl]; omega
      have hren := ren x Y n r hYl
        (fun w hw => by simp only [r]; rw [hxl] at hw; rw [if_neg (by omega), if_neg (by omega)])
        (fun w hw => by
          rw [hYl]; rw [hxl] at hw; simp only [r]; split_ifs <;> omega)
        (fun w hw => by
          rw [hxl] at hw
          have hrw : r w < N := by simp only [r, N]; split_ifs <;> omega
          simp only [Y]
          rw [getD_prefix _ _ _ (by rw [hx'l]; exact hrw), hx']
          simp only [x]
          rw [inp_getD]
          simp only [P, Finset.mem_filter, Finset.mem_range, decide_eq_decide]
          constructor
          · rintro ⟨_, h⟩; exact ⟨hw, hw, h⟩
          · rintro ⟨_, _, h⟩; exact ⟨hrw, h⟩) C.gates
      have hguard : Y.getD (acc N (n - 1)) false = decide (u.val ≤ n - 1) := by
        apply chain_val N u.val x' hx'l (n - 1) (by omega)
        intro i hi
        rw [hx']
        simp only [decide_eq_decide]
        omega
      have hacclt : acc N (n - 1) < Y.length := by
        rw [hYl, hxl]; simp only [acc, N]; split_ifs <;> omega
      show (wiresFrom G x').getD (N + (n - 1) + C.gates.length) false = _
      simp only [G]
      rw [wiresFrom_snoc, getD_snoc, wiresFrom_append, length_wiresFrom, length_wiresFrom,
        chain_length, hx'l, List.length_map, if_pos rfl]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
        Bool.and_true]
      change ((wiresFrom (C.gates.map (rg r)) Y).getD (r C.output) false &&
        (wiresFrom (C.gates.map (rg r)) Y).getD (acc N (n - 1)) false) = _
      rw [hren C.output, getD_prefix _ _ _ hacclt, hguard]
      by_cases h : u.val < n
      · rw [dif_pos h]
        have hxe : x = oneEach (⟨u.val, h⟩ : Fin n) v := by
          rw [oneEach_eq]
          simp only [x]
          congr 1
          ext w
          simp only [P, r, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
            Finset.mem_singleton]
          constructor
          · rintro ⟨h1, h2⟩
            split_ifs at h2 <;> omega
          · intro h2
            refine ⟨by omega, ?_⟩
            split_ifs <;> omega
        have : decide (u.val ≤ n - 1) = true := by simp only [decide_eq_true_eq]; omega
        rw [this, Bool.and_true, ← hR ⟨u.val, h⟩ v, hxe]
        rfl
      · rw [dif_neg h]
        have : decide (u.val ≤ n - 1) = false := by simp only [decide_eq_false_iff_not]; omega
        rw [this, Bool.and_false]

end PEqualNP.Outside.L_meta_33599

open PEqualNP.Outside.L_meta_33599 in
theorem PEqualNP.Outside.L_meta_33599 : (∀ (n m s : Nat) (A : Fin n → Fin m → Bool),
  PEqualNP.Represents.RepSizeAtMost A s →
  PEqualNP.Represents.RepSizeAtMost
    (fun (i : Fin (n+1)) j => if h : i.val < n then A ⟨i.val,h⟩ j else false) (s+n)) ∧
(∀ n s : Nat,
  PEqualNP.Represents.RepSizeAtMost
    (fun (_ : Fin n) (j : Fin 2) => decide (j.val = 0)) 0 ∧
  (PEqualNP.Represents.RepSizeAtMost
    (fun (i : Fin (n+1)) (j : Fin 2) => decide (i.val < n ∧ j.val = 0)) s ↔ n ≤ s)) := by
  have h2a : ∀ n : ℕ, PEqualNP.Represents.RepSizeAtMost
      (fun (_ : Fin n) (j : Fin 2) => decide (j.val = 0)) 0 := by
    intro n
    refine ⟨⟨[], n⟩, fun g hg => by simp at hg, by simp [PEqualNP.CircuitLowerBounds.Circuit.size],
      fun u v => ?_⟩
    have hu := u.2
    show (PEqualNP.Represents.oneEach u v).getD n false = _
    rw [PEqualNP.Outside.L_meta_33599.oneEach_eq, PEqualNP.Outside.L_meta_33599.inp_getD]
    have hv := v.2
    simp only [Finset.mem_insert, Finset.mem_singleton, decide_eq_decide]
    omega
  refine ⟨part1, fun n s => ⟨h2a n, ?_, ?_⟩⟩
  · intro h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · omega
    have H := PEqualNP.Outside.L_meta_33599.reads_le _ h
    have hL : n ≤ (PEqualNP.Outside.L_meta_33599.forcedL
        (fun (i : Fin (n+1)) (j : Fin 2) => decide (i.val < n ∧ j.val = 0))).card := by
      have hsub : (Finset.univ : Finset (Fin n)).map Fin.castSuccEmb ⊆
          PEqualNP.Outside.L_meta_33599.forcedL
            (fun (i : Fin (n+1)) (j : Fin 2) => decide (i.val < n ∧ j.val = 0)) := by
        intro u hu
        obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 hu
        simp only [PEqualNP.Outside.L_meta_33599.forcedL, Finset.mem_filter,
          Finset.mem_univ, true_and]
        refine ⟨0, ?_, Fin.last n, ?_⟩
        · simp
        · simp
      have := Finset.card_le_card hsub
      simpa using this
    have hR : 1 ≤ (PEqualNP.Outside.L_meta_33599.forcedR
        (fun (i : Fin (n+1)) (j : Fin 2) => decide (i.val < n ∧ j.val = 0))).card := by
      apply Finset.card_pos.2
      refine ⟨0, ?_⟩
      simp only [PEqualNP.Outside.L_meta_33599.forcedR, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨⟨0, by omega⟩, by simp [hn], 1, by simp⟩
    omega
  · intro h
    have H := part1 n 2 0 _ (h2a n)
    have he : (fun (i : Fin (n+1)) (j : Fin 2) =>
        if h : i.val < n then (fun (_ : Fin n) (j : Fin 2) => decide (j.val = 0)) ⟨i.val,h⟩ j
        else false) =
        (fun (i : Fin (n+1)) (j : Fin 2) => decide (i.val < n ∧ j.val = 0)) := by
      funext i j
      by_cases hi : i.val < n
      · simp [hi]
      · simp [hi]
    rw [he] at H
    obtain ⟨C, h1, h2, h3⟩ := H
    exact ⟨C, h1, by omega, h3⟩
