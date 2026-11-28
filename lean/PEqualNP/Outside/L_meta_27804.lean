import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_6158

namespace PEqualNP.Outside.L_meta_27804.Helpers

open PEqualNP.CircuitLowerBounds

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

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

end PEqualNP.Outside.L_meta_27804.Helpers

namespace PEqualNP.Outside.L_meta_27804.RepReads

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_27804.Helpers
open PEqualNP.Represents

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

def forcedL {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun u => ∃ v, A u v = true ∧ ∃ u', A u' v = false

def forcedR {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun v => ∃ u, A u v = true ∧ ∃ w, A u w = false

theorem reads_le {n m s : ℕ} (A : Fin n → Fin m → Bool) (h : RepSizeAtMost A s) :
    (forcedL A).card + (forcedR A).card ≤ s + 1 := by
  obtain ⟨C, hC, hs, hR⟩ := h
  obtain ⟨S, hcard, hS⟩ := needed (n + m) C.gates (fun g hg => (hC g hg).2) {C.output}
  have hop : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
    fun g hg => (hC g hg).1
  have hev : ∀ P, C.eval (inp (n + m) P) =
      (wiresFrom C.gates (inp (n + m) P)).getD C.output false := fun P => rfl

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

end PEqualNP.Outside.L_meta_27804.RepReads

namespace PEqualNP.Outside.L_meta_27804.RepInduced

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_27804.Helpers
open PEqualNP.Represents PEqualNP.Outside.L_meta_27804.RepReads

open scoped Classical

section kill
variable (N : ℕ) (Z : Finset ℕ) (gs : List Gate)

def gat (j : ℕ) : Gate := gs.getD j ⟨.and, []⟩

noncomputable def st : ℕ → List Gate × (ℕ → Option ℕ)
  | 0 => ([], fun w => if w < N ∧ w ∉ Z then some w else none)
  | j + 1 =>
    let p := st j
    let g := gat gs j
    if ∃ i ∈ g.inputs, p.2 i = none then
      (p.1, Function.update p.2 (N + j)
        (if g.op = GateOp.and then none else (g.inputs.filterMap p.2).head?))
    else (p.1 ++ [⟨g.op, g.inputs.map fun i => (p.2 i).getD 0⟩],
      Function.update p.2 (N + j) (some (N + p.1.length)))

def Dead (j : ℕ) : Prop := ∃ i ∈ (gat gs j).inputs, (st N Z gs j).2 i = none

theorem st_dead {j : ℕ} (h : Dead N Z gs j) : st N Z gs (j + 1) =
    ((st N Z gs j).1, Function.update (st N Z gs j).2 (N + j)
      (if (gat gs j).op = GateOp.and then none
        else ((gat gs j).inputs.filterMap (st N Z gs j).2).head?)) := by
  rw [st]; exact if_pos h

theorem st_keep {j : ℕ} (h : ¬ Dead N Z gs j) : st N Z gs (j + 1) =
    ((st N Z gs j).1 ++ [⟨(gat gs j).op, (gat gs j).inputs.map fun i =>
      ((st N Z gs j).2 i).getD 0⟩],
      Function.update (st N Z gs j).2 (N + j) (some (N + (st N Z gs j).1.length))) := by
  rw [st]; exact if_neg h

theorem st_ne {j w : ℕ} (h : w ≠ N + j) : (st N Z gs (j + 1)).2 w = (st N Z gs j).2 w := by
  by_cases hd : Dead N Z gs j
  · rw [st_dead N Z gs hd]; exact Function.update_of_ne h _ _
  · rw [st_keep N Z gs hd]; exact Function.update_of_ne h _ _

theorem st_late (j : ℕ) : ∀ w, N + j ≤ w → (st N Z gs j).2 w = none := by
  induction j with
  | zero => intro w h; simp [st, show ¬ w < N by omega]
  | succ j ih => intro w h; rw [st_ne N Z gs (by omega)]; exact ih w (by omega)

theorem st_final {j k w : ℕ} (hjk : j ≤ k) (h : w < N + j) :
    (st N Z gs k).2 w = (st N Z gs j).2 w := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [st_ne N Z gs (by omega)]; exact ih

theorem st_off {j k w : ℕ} (hjk : j ≤ k) (h : (st N Z gs k).2 w = none) :
    (st N Z gs j).2 w = none := by
  by_cases hw : w < N + j
  · rw [← st_final N Z gs hjk hw]; exact h
  · exact st_late N Z gs j w (by omega)

theorem st_len (j : ℕ) : (st N Z gs j).1.length +
    ((Finset.range j).filter fun i => Dead N Z gs i).card = j := by
  induction j with
  | zero => simp [st]
  | succ j ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hd : Dead N Z gs j
    · rw [if_pos hd, Finset.card_insert_of_notMem (by simp), st_dead N Z gs hd]
      show (st N Z gs j).1.length + _ = _
      omega
    · rw [if_neg hd, st_keep N Z gs hd]
      simp only [List.length_append, List.length_singleton]
      omega

theorem st_lt (j : ℕ) : ∀ w a, (st N Z gs j).2 w = some a → a < N + (st N Z gs j).1.length := by
  induction j with
  | zero =>
    intro w a h
    simp only [st] at h
    split_ifs at h with hw
    · simp only [Option.some.injEq] at h
      simp [st]; omega
  | succ j ih =>
    intro w a h
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd] at h ⊢
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self] at h
        split_ifs at h
        have hm := List.mem_of_mem_head? (Option.mem_def.2 h)
        obtain ⟨i, _, hi⟩ := List.mem_filterMap.1 hm
        exact ih i a hi
      · simp only [Function.update_of_ne hw] at h
        exact ih w a h
    · rw [st_keep N Z gs hd] at h ⊢
      simp only [List.length_append, List.length_singleton]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, Option.some.injEq] at h
        omega
      · simp only [Function.update_of_ne hw] at h
        have := ih w a h
        omega

variable (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)

include hgs in
theorem gat_ok (j : ℕ) : ((gat gs j).op = GateOp.and ∨ (gat gs j).op = GateOp.or) ∧
    (gat gs j).inputs.length ≤ 2 := by
  by_cases h : j < gs.length
  · have := hgs (gat gs j) (by rw [gat, List.getD_eq_getElem _ _ h]; exact List.getElem_mem h)
    simpa using this
  · rw [gat, List.getD_eq_default _ _ (by omega)]; simp

include hgs in
theorem st_ok (j : ℕ) : ∀ g ∈ (st N Z gs j).1,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction j with
  | zero => simp [st]
  | succ j ih =>
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd]; exact ih
    · rw [st_keep N Z gs hd]
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact ih g hg
      · rw [List.mem_singleton.1 hg]
        have := gat_ok gs hgs j
        simpa using this

theorem take_succ (j : ℕ) (hj : j < gs.length) : gs.take (j + 1) = gs.take j ++ [gat gs j] := by
  rw [List.take_succ_eq_append_getElem hj, gat, List.getD_eq_getElem _ _ hj]

include hgs in

theorem st_val (P : Finset ℕ) (j : ℕ) (hj : j ≤ gs.length) : ∀ w,
    ((st N Z gs j).2 w = none → (wiresFrom (gs.take j) (inp N (P \ Z))).getD w false = false) ∧
    ∀ a, (st N Z gs j).2 w = some a → (wiresFrom (st N Z gs j).1 (inp N P)).getD a false =
      (wiresFrom (gs.take j) (inp N (P \ Z))).getD w false := by
  induction j with
  | zero =>
    intro w
    simp only [st, List.take_zero, wiresFrom, List.foldl_nil, inp_getD, Finset.mem_sdiff]
    constructor
    · intro h
      split_ifs at h with hw
      simp only [decide_eq_false_iff_not]; tauto
    · intro a h
      split_ifs at h with hw
      simp only [Option.some.injEq] at h
      subst h
      rw [decide_eq_decide]; tauto
  | succ j ih =>
    have H := ih (by omega)
    have hl1 : (wiresFrom (gs.take j) (inp N (P \ Z))).length = N + j := by
      rw [length_wiresFrom, List.length_take]; simp [inp]; omega
    have hl2 : (wiresFrom (st N Z gs j).1 (inp N P)).length = N + (st N Z gs j).1.length := by
      rw [length_wiresFrom]; simp [inp]
    have hok := gat_ok gs hgs j
    rw [take_succ gs j (by omega), wiresFrom_snoc]
    set V := wiresFrom (gs.take j) (inp N (P \ Z)) with hV
    intro w
    rw [getD_snoc, hl1]
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, if_true]
        obtain ⟨i, hi, hoff⟩ := hd
        have hi0 := (H i).1 hoff
        rcases hok.1 with hop | hop
        · simp only [hop, if_true]
          refine ⟨fun _ => ?_, fun a h => by simp at h⟩
          rw [← Bool.not_eq_true, GateOp.eval, List.all_eq_true]
          intro h
          have := h _ (List.mem_map.2 ⟨i, hi, rfl⟩)
          rw [hi0] at this; simp at this
        · simp only [hop, reduceCtorEq, if_false]

          have hlen := hok.2
          constructor
          · intro h
            rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff] at h
            rw [← Bool.not_eq_true, GateOp.eval, List.any_eq_true]
            rintro ⟨b, hb, hb1⟩
            obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hb
            have := (H i').1 (h i' hi')
            rw [this] at hb1; simp at hb1
          · intro a h
            obtain ⟨i', hi', hia⟩ := List.mem_filterMap.1 (List.mem_of_mem_head? (Option.mem_def.2 h))
            rw [(H i').2 a hia, GateOp.eval]
            have hne : i ≠ i' := by rintro rfl; rw [hoff] at hia; simp at hia

            have hall : ∀ b ∈ (gat gs j).inputs, b = i ∨ b = i' := by
              intro b hb
              by_contra hn
              push Not at hn
              have h3 : ({i, i', b} : Finset ℕ) ⊆ (gat gs j).inputs.toFinset := by
                intro c hc
                simp only [Finset.mem_insert, Finset.mem_singleton] at hc
                rcases hc with rfl | rfl | rfl <;> simpa
              have := Finset.card_le_card h3
              rw [Finset.card_eq_three.2 ⟨i, i', b, hne, fun e => hn.1 e.symm, fun e => hn.2 e.symm,
                rfl⟩] at this
              have := List.toFinset_card_le (gat gs j).inputs
              omega
            apply Bool.eq_iff_iff.2
            rw [List.any_eq_true]
            constructor
            · intro hv; exact ⟨_, List.mem_map.2 ⟨i', hi', rfl⟩, hv⟩
            · rintro ⟨b, hb, hb1⟩
              obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
              rcases hall c hc with rfl | rfl
              · rw [hi0] at hb1; simp at hb1
              · exact hb1
      · simp only [Function.update_of_ne hw, if_neg hw]
        exact H w
    · rw [st_keep N Z gs hd]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, if_true]
        refine ⟨fun h => by simp at h, fun a h => ?_⟩
        simp only [Option.some.injEq] at h
        subst h
        rw [wiresFrom_snoc, getD_snoc, hl2, if_pos rfl]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        obtain ⟨b, hb⟩ : ∃ b, (st N Z gs j).2 i = some b := by
          cases h : (st N Z gs j).2 i with
          | none => exact absurd ⟨i, hi, h⟩ hd
          | some b => exact ⟨b, rfl⟩
        simp only [Function.comp_apply, hb, Option.getD_some]
        exact (H i).2 b hb
      · simp only [Function.update_of_ne hw, if_neg hw]
        refine ⟨(H w).1, fun a h => ?_⟩
        have hlt := st_lt N Z gs j w a h
        rw [wiresFrom_snoc, getD_snoc, hl2, if_neg (by omega)]
        exact (H w).2 a h

def Live (o : ℕ) : ℕ → Prop :=
  Relation.ReflTransGen (fun g w => ∃ j < gs.length, g = N + j ∧ w ∈ (gat gs j).inputs) o

theorem live_dep (o : ℕ) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (h : ∀ i, Live N gs o i → x.getD i false = y.getD i false) (j : ℕ) (hj : j ≤ gs.length) :
    ∀ w, Live N gs o w →
      (wiresFrom (gs.take j) x).getD w false = (wiresFrom (gs.take j) y).getD w false := by
  induction j with
  | zero => intro w hw; simpa [wiresFrom] using h w hw
  | succ j ih =>
    intro w hw
    have H := ih (by omega)
    rw [take_succ gs j (by omega), wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc,
      length_wiresFrom, length_wiresFrom, hx, hy, List.length_take, Nat.min_eq_left (by omega)]
    split_ifs with hwj
    · congr 1
      apply List.map_congr_left
      intro a ha
      exact H a (hw.tail ⟨j, by omega, hwj, ha⟩)
    · exact H w hw

include hgs in

theorem kill_count (o : ℕ) (Z0 : Finset ℕ) (hZ0 : ∀ i ∈ Z0, i < N ∧ i ∈ Z ∧ Live N gs o i)
    (ho : (st N Z gs gs.length).2 o ≠ none) :
    Z0.card ≤ ((Finset.range gs.length).filter fun i => Dead N Z gs i).card := by
  set k := gs.length with hk
  let K := (Finset.range k).filter fun j => Dead N Z gs j ∧ Live N gs o (N + j)
  let Y := (Finset.range k).filter fun j => (st N Z gs k).2 (N + j) = none ∧ Live N gs o (N + j)
  let Q : Finset (Σ _ : ℕ, ℕ) := K.sigma fun j =>
    (gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none
  let W := Z0 ∪ Y.image fun j => N + j
  have hYK : Y ⊆ K := by
    intro j hj
    obtain ⟨hjk, hz, hl⟩ := Finset.mem_filter.1 hj
    refine Finset.mem_filter.2 ⟨hjk, ?_, hl⟩
    by_contra hd
    have hjk' := Finset.mem_range.1 hjk
    rw [st_final N Z gs (show j + 1 ≤ k by omega) (by omega), st_keep N Z gs hd] at hz
    simp at hz
  have hW : W ⊆ Q.image fun q => q.2 := by
    intro w hw
    have hw2 : (st N Z gs k).2 w = none ∧ Live N gs o w := by
      rcases Finset.mem_union.1 hw with h | h
      · obtain ⟨h1, h2, h3⟩ := hZ0 w h
        refine ⟨?_, h3⟩
        rw [st_final N Z gs (Nat.zero_le k) (by omega)]
        simp [st, h2]
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h
        exact (Finset.mem_filter.1 hj).2
    have hne : w ≠ o := fun e => ho (e ▸ hw2.1)
    rcases Relation.ReflTransGen.cases_tail hw2.2 with e | ⟨g, hg, j, hj, rfl, hi⟩
    · exact absurd e hne
    · have hoff := st_off N Z gs (show j ≤ k by omega) hw2.1
      refine Finset.mem_image.2 ⟨⟨j, w⟩, Finset.mem_sigma.2 ⟨?_, ?_⟩, rfl⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, ⟨w, hi, hoff⟩, hg⟩
      · exact Finset.mem_filter.2 ⟨List.mem_toFinset.2 hi, hoff⟩
  have hWc : W.card = Z0.card + Y.card := by
    have : Disjoint Z0 (Y.image fun j => N + j) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 h2
      have := (hZ0 _ h1).1
      omega
    show (Z0 ∪ Y.image fun j => N + j).card = _
    rw [Finset.card_union_of_disjoint this,
      Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  have hQ : Q.card ≤ K.card + Y.card := by
    show (K.sigma _).card ≤ _
    rw [Finset.card_sigma]
    calc ∑ j ∈ K, ((gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none).card
        ≤ ∑ j ∈ K, (1 + if j ∈ Y then 1 else 0) := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨hjk, hd, hl⟩ := Finset.mem_filter.1 hj
          have hjk' := Finset.mem_range.1 hjk
          have hok := gat_ok gs hgs j
          have hc := List.toFinset_card_le (gat gs j).inputs
          have hf := Finset.card_filter_le (gat gs j).inputs.toFinset
            fun i => (st N Z gs j).2 i = none
          split_ifs with hY
          · omega
          ·
            have hsome : (st N Z gs k).2 (N + j) ≠ none := fun e =>
              hY (Finset.mem_filter.2 ⟨hjk, e, hl⟩)
            rw [st_final N Z gs (show j + 1 ≤ k by omega) (by omega), st_dead N Z gs hd] at hsome
            simp only [Function.update_self] at hsome
            obtain ⟨i, hi, hia⟩ : ∃ i ∈ (gat gs j).inputs, (st N Z gs j).2 i ≠ none := by
              by_contra hn
              push Not at hn
              apply hsome
              split_ifs
              · rfl
              · rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff]; exact hn
            have hlt : ((gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none).card <
                (gat gs j).inputs.toFinset.card :=
              Finset.card_lt_card (Finset.filter_ssubset.2 ⟨i, List.mem_toFinset.2 hi, hia⟩)
            omega
      _ = K.card + Y.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_ite_mem,
            Finset.inter_eq_right.2 hYK, Finset.sum_const, smul_eq_mul, mul_one]
  have h1 := Finset.card_le_card hW
  have h2 := Finset.card_image_le (s := Q) (f := fun q => q.2)
  have h3 : K.card ≤ ((Finset.range k).filter fun i => Dead N Z gs i).card :=
    Finset.card_le_card fun j hj => by
      obtain ⟨a, b, _⟩ := Finset.mem_filter.1 hj
      exact Finset.mem_filter.2 ⟨a, b⟩
  omega

include hgs in

theorem kill (o : ℕ) (Z0 : Finset ℕ) (hZ0 : ∀ i ∈ Z0, i < N ∧ i ∈ Z ∧ Live N gs o i)
    (P0 : Finset ℕ) (hP0 : Circuit.eval ⟨gs, o⟩ (inp N (P0 \ Z)) = true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + Z0.card ≤ gs.length ∧
      ∀ P, D.eval (inp N P) = Circuit.eval ⟨gs, o⟩ (inp N (P \ Z)) := by
  have hv : ∀ P, _ := fun P => st_val N Z gs hgs P gs.length le_rfl o
  simp only [List.take_length] at hv
  have ho : (st N Z gs gs.length).2 o ≠ none := by
    intro e
    have := (hv P0).1 e
    rw [show Circuit.eval ⟨gs, o⟩ (inp N (P0 \ Z)) =
      (wiresFrom gs (inp N (P0 \ Z))).getD o false from rfl, this] at hP0
    exact Bool.noConfusion hP0
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 ho
  refine ⟨⟨(st N Z gs gs.length).1, a⟩, st_ok N Z gs hgs _, ?_, fun P => (hv P).2 a ha⟩
  have h1 := kill_count N Z gs hgs o Z0 hZ0 ho
  have h2 := st_len N Z gs gs.length
  show (st N Z gs gs.length).1.length + Z0.card ≤ gs.length
  omega

end kill

theorem induced : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (R : Finset (Fin n)) (K : Finset (Fin m)), (∀ u ∈ R, ∃ v ∈ K, A u v = false) → (∀ v ∈ K, ∃ u ∈ R, A u v = false) → (∃ u ∈ R, ∃ v ∈ K, A u v = true) → PEqualNP.Represents.RepSizeAtMost A s → ∃ s' : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v => A u v && decide (u ∈ R) && decide (v ∈ K)) s' ∧ s' + ((Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card + (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)).card) ≤ s + ((R.filter (fun a => ∃ b ∈ K, A a b = true)).card + (K.filter (fun b => ∃ a ∈ R, A a b = true)).card) := by
  intro n m s A R K hR hK ⟨u0, hu0, v0, hv0, h0⟩ ⟨⟨gs, o⟩, hC, hs, hrep⟩
  let BL := R.filter fun a => ∃ b ∈ K, A a b = true
  let BR := K.filter fun b => ∃ a ∈ R, A a b = true
  let Z : Finset ℕ := (Finset.univ.filter fun a : Fin n => a ∉ BL).image (fun a : Fin n => (a : ℕ)) ∪
    (Finset.univ.filter fun b : Fin m => b ∉ BR).image (fun b : Fin m => n + (b : ℕ))
  have hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := hC
  have hop : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := fun g hg => (hC g hg).1
  have hZl : ∀ a : Fin n, (a : ℕ) ∈ Z ↔ a ∉ BL := by
    intro a
    simp only [Z, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨x, hx, e⟩ | ⟨x, _, e⟩)
      · rwa [← Fin.ext e]
      · have := a.2; omega
    · exact fun h => Or.inl ⟨a, h, rfl⟩
  have hZr : ∀ b : Fin m, n + (b : ℕ) ∈ Z ↔ b ∉ BR := by
    intro b
    simp only [Z, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨x, _, e⟩ | ⟨x, hx, e⟩)
      · have := x.2; omega
      · rwa [← Fin.ext (show (x : ℕ) = b by omega)]
    · exact fun h => Or.inr ⟨b, h, rfl⟩
  have hmono : ∀ P Q : Finset ℕ, P ⊆ Q → Circuit.eval ⟨gs, o⟩ (inp (n + m) P) = true →
      Circuit.eval ⟨gs, o⟩ (inp (n + m) Q) = true := by
    intro P Q hPQ
    refine mono gs hop _ _ (by simp [inp]) (fun i => ?_) _
    rw [inp_getD, inp_getD, decide_eq_true_eq, decide_eq_true_eq]
    exact fun ⟨a, b⟩ => ⟨a, hPQ b⟩
  have hA : ∀ (u : Fin n) (v : Fin m),
      Circuit.eval ⟨gs, o⟩ (inp (n + m) {(u : ℕ), n + (v : ℕ)}) = A u v := by
    intro u v; rw [← oneEach_eq]; exact hrep u v
  have hoff : ∀ P w, ¬ Live (n + m) gs o w →
      Circuit.eval ⟨gs, o⟩ (inp (n + m) P) = Circuit.eval ⟨gs, o⟩ (inp (n + m) (P.erase w)) := by
    intro P w hw
    have := live_dep (n + m) gs o (inp (n + m) P) (inp (n + m) (P.erase w)) (by simp [inp])
      (by simp [inp]) (fun i hi => by
        rw [inp_getD, inp_getD, decide_eq_decide, Finset.mem_erase]
        have : i ≠ w := fun e => hw (e ▸ hi)
        tauto) gs.length le_rfl o Relation.ReflTransGen.refl
    rw [List.take_length] at this
    exact this
  have hL : ∀ u ∈ forcedL A, Live (n + m) gs o (u : ℕ) := by
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
  have hRr : ∀ v ∈ forcedR A, Live (n + m) gs o (n + (v : ℕ)) := by
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
  have hBL : BL ⊆ forcedL A := by
    intro a ha
    obtain ⟨_, b, hb, hab⟩ := Finset.mem_filter.1 ha
    obtain ⟨a', _, ha'⟩ := hK b hb
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, b, hab, a', ha'⟩
  have hBR : BR ⊆ forcedR A := by
    intro b hb
    obtain ⟨_, a, ha, hab⟩ := Finset.mem_filter.1 hb
    obtain ⟨b', _, hb'⟩ := hR a ha
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, a, hab, b', hb'⟩
  let Z0 : Finset ℕ := (forcedL A \ BL).image (fun a : Fin n => (a : ℕ)) ∪
    (forcedR A \ BR).image (fun b : Fin m => n + (b : ℕ))
  have hZ0 : ∀ i ∈ Z0, i < n + m ∧ i ∈ Z ∧ Live (n + m) gs o i := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 ha
      exact ⟨by have := a.2; omega, (hZl a).2 h2, hL a h1⟩
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hb
      exact ⟨by have := b.2; omega, (hZr b).2 h2, hRr b h1⟩
  have hZ0c : Z0.card = (forcedL A \ BL).card + (forcedR A \ BR).card := by
    have hdis : Disjoint ((forcedL A \ BL).image (fun a : Fin n => (a : ℕ)))
        ((forcedR A \ BR).image (fun b : Fin m => n + (b : ℕ))) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 h1
      obtain ⟨v, _, hv⟩ := Finset.mem_image.1 h2
      have := u.2
      omega
    show (_ ∪ _ : Finset ℕ).card = _
    rw [Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))]

  have hval : ∀ (u : Fin n) (v : Fin m),
      Circuit.eval ⟨gs, o⟩ (inp (n + m) (({(u : ℕ), n + (v : ℕ)} : Finset ℕ) \ Z)) =
        (A u v && decide (u ∈ R) && decide (v ∈ K)) := by
    intro u v
    by_cases hu : u ∈ BL
    · by_cases hv : v ∈ BR
      · have hu' := (Finset.mem_filter.1 hu).1
        have hv' := (Finset.mem_filter.1 hv).1
        rw [show ({(u : ℕ), n + (v : ℕ)} : Finset ℕ) \ Z = {(u : ℕ), n + (v : ℕ)} from by
          rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_left]
          intro i hi
          rcases Finset.mem_insert.1 hi with rfl | hi
          · rw [hZl]; exact fun h => h hu
          · rw [Finset.mem_singleton.1 hi, hZr]; exact fun h => h hv, hA]
        simp [hu', hv']
      ·
        have hu' := (Finset.mem_filter.1 hu).1
        obtain ⟨b, hb, hab⟩ := hR u hu'
        have e1 : (A u v && decide (u ∈ R) && decide (v ∈ K)) = false := by
          by_contra hne
          simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hne
          exact hv (Finset.mem_filter.2 ⟨hne.2, u, hne.1.2, hne.1.1⟩)
        rw [e1]
        by_contra hne
        rw [Bool.not_eq_false] at hne
        have := hmono _ {(u : ℕ), n + (b : ℕ)} (fun i hi => by
          obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
          rcases Finset.mem_insert.1 h1 with rfl | h1
          · simp
          · rw [Finset.mem_singleton.1 h1] at h2; exact absurd ((hZr v).2 hv) h2) hne
        rw [hA, hab] at this
        exact Bool.noConfusion this
    ·
      have e1 : (A u v && decide (u ∈ R) && decide (v ∈ K)) = false := by
        by_contra hne
        simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hne
        exact hu (Finset.mem_filter.2 ⟨hne.1.2, v, hne.2, hne.1.1⟩)
      rw [e1]
      by_contra hne
      rw [Bool.not_eq_false] at hne
      obtain ⟨b, hb, a, hab⟩ : ∃ b : Fin m, (n + (v : ℕ) ∉ Z → b = v) ∧ ∃ a : Fin n, A a b = false := by
        by_cases hv : v ∈ BR
        · obtain ⟨a, _, ha⟩ := hK v (Finset.mem_filter.1 hv).1
          exact ⟨v, fun _ => rfl, a, ha⟩
        · obtain ⟨a, _, ha⟩ := hK v0 hv0
          exact ⟨v0, fun h => absurd ((hZr v).2 hv) h, a, ha⟩
      have := hmono _ {(a : ℕ), n + (b : ℕ)} (fun i hi => by
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
        rcases Finset.mem_insert.1 h1 with rfl | h1
        · exact absurd ((hZl u).2 hu) h2
        · rw [Finset.mem_singleton.1 h1] at h2 ⊢
          rw [hb h2]; simp) hne
      rw [hA, hab] at this
      exact Bool.noConfusion this
  obtain ⟨D, hD1, hD2, hD3⟩ := kill (n + m) Z gs hgs o Z0 hZ0 {(u0 : ℕ), n + (v0 : ℕ)}
    (by rw [hval]; simp [h0, hu0, hv0])
  refine ⟨D.size, ⟨D, hD1, le_rfl, fun u v => ?_⟩, ?_⟩
  · rw [oneEach_eq, hD3, hval]
  · have c1 := Finset.card_sdiff_add_card_eq_card hBL
    have c2 := Finset.card_sdiff_add_card_eq_card hBR
    have hs' : gs.length ≤ s := hs
    have e1 : (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧
      ∃ a' : Fin n, A a' b = false)).card = (forcedL A).card := by unfold forcedL; congr
    have e2 : (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧
      ∃ b' : Fin m, A a b' = false)).card = (forcedR A).card := by unfold forcedR; congr
    have e3 : (R.filter (fun a => ∃ b ∈ K, A a b = true)).card = BL.card := by congr
    have e4 : (K.filter (fun b => ∃ a ∈ R, A a b = true)).card = BR.card := by congr
    rw [e1, e2]
    try rw [e3, e4]
    omega

end PEqualNP.Outside.L_meta_27804.RepInduced

namespace PEqualNP.Outside.L_meta_27804

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_27804.Helpers PEqualNP.Outside.L_meta_27804.RepReads

def A0 (n m : ℕ) (u : Fin n) (v : Fin m) : Bool := (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)

def remap (n m K : ℕ) (i : ℕ) : ℕ :=
  if i < 4 then i else if i < n then 8 + K else if i < n + 4 then i - n + 4
  else if i < n + m then 8 + K else i - (n + m) + 8

def mapGate (n m K : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (remap n m K)⟩

def shrink (n m : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (mapGate n m C.gates.length), remap n m C.gates.length C.output⟩

def Rel (n m K k : ℕ) (W W' : List Bool) : Prop :=
  W.length = n + m + k ∧ W'.length = 8 + k ∧ ∀ i, W.getD i false = W'.getD (remap n m K i) false

theorem remap_eq (n m K k i : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) (hk : k < K) :
    remap n m K i = 8 + k ↔ i = n + m + k := by
  unfold remap; split_ifs <;> omega

theorem rel_step (n m K k : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) (hk : k < K) (W W' : List Bool)
    (h : Rel n m K k W W') (g : Gate) :
    Rel n m K (k + 1) (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)])
      (W' ++ [(mapGate n m K g).op.eval ((mapGate n m K g).inputs.map fun i => W'.getD i false)]) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simp [h1]; omega, by simp [h2]; omega, ?_⟩
  intro i
  rw [getD_snoc, getD_snoc]
  have e : (g.inputs.map fun i => W.getD i false) =
      ((mapGate n m K g).inputs.map fun i => W'.getD i false) := by
    simp only [mapGate, List.map_map]
    apply List.map_congr_left
    intro j _
    simpa using h3 j
  by_cases hi : i = n + m + k
  · have : remap n m K i = W'.length := by rw [h2]; exact (remap_eq n m K k i hn hm hk).mpr hi
    rw [if_pos (by rw [h1]; exact hi), if_pos this, e]
    rfl
  · have : remap n m K i ≠ W'.length := by
      rw [h2]; intro hc; exact hi ((remap_eq n m K k i hn hm hk).mp hc)
    rw [if_neg (by rw [h1]; exact hi), if_neg this, h3 i]

theorem rel_run (n m K : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) (gs : List Gate) :
    ∀ k W W', k + gs.length ≤ K → Rel n m K k W W' →
      Rel n m K (k + gs.length) (wiresFrom gs W) (wiresFrom (gs.map (mapGate n m K)) W') := by
  induction gs with
  | nil => intro k W W' _ h; simpa [wiresFrom] using h
  | cons g gs ih =>
    intro k W W' hk h
    have := ih (k + 1) _ _ (by simp at hk; omega)
      (rel_step n m K k hn hm (by simp at hk; omega) W W' h g)
    have e : k + 1 + gs.length = k + (g :: gs).length := by simp; omega
    rw [e] at this
    exact this

theorem rel_init (n m K : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) (u v : ℕ) (hu : u < 4) (hv : v < 4) :
    Rel n m K 0 (inp (n + m) {u, n + v}) (inp (4 + 4) {u, 4 + v}) := by
  refine ⟨by simp [inp], by simp [inp], ?_⟩
  intro i
  rw [inp_getD, inp_getD]
  unfold remap
  split_ifs <;> simp only [Finset.mem_insert, Finset.mem_singleton, decide_eq_decide] <;>
    constructor <;> intro h <;> omega

theorem shrink_eval (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) (C : Circuit) (u v : ℕ) (hu : u < 4)
    (hv : v < 4) :
    (shrink n m C).eval (inp (4 + 4) {u, 4 + v}) = C.eval (inp (n + m) {u, n + v}) := by
  have := rel_run n m C.gates.length hn hm C.gates 0 _ _ (by simp)
    (rel_init n m C.gates.length hn hm u v hu hv)
  unfold Circuit.eval
  rw [wires_eq, wires_eq, this.2.2 C.output]
  rfl

theorem shrink_mono (n m : ℕ) (C : Circuit) (h : Monotone2 C) : Monotone2 (shrink n m C) := by
  intro g hg
  simp only [shrink, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  obtain ⟨h1, h2⟩ := h g0 hg0
  exact ⟨h1, by simpa [mapGate] using h2⟩

theorem shrink_size (n m : ℕ) (C : Circuit) : (shrink n m C).size = C.size := by
  simp [shrink, Circuit.size]

theorem core_lower (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) (s : ℕ) (hs : s ≤ 6)
    (h : RepSizeAtMost (fun (u : Fin n) (v : Fin m) =>
      A0 n m u v && decide (u ∈ Finset.univ.filter (fun a : Fin n => a.val < 3)) &&
        decide (v ∈ Finset.univ.filter (fun b : Fin m => b.val < 3))) s) : False := by
  obtain ⟨C, hmo, hsz, hrep⟩ := h
  apply (PEqualNP.Outside.L_meta_6158).2
  refine ⟨shrink n m C, shrink_mono n m C hmo, by rw [shrink_size]; omega, ?_⟩
  intro u v
  have e1 := oneEach_eq u v
  have hu := u.2
  have hv := v.2
  rw [e1, shrink_eval n m hn hm C u v hu hv]
  have := hrep ⟨u.val, by omega⟩ ⟨v.val, by omega⟩
  rw [oneEach_eq] at this
  simp only at this
  rw [this]
  simp only [A0, Finset.mem_filter, Finset.mem_univ, true_and]
  have key : ∀ a b : Fin 4, ((64478 : Nat).testBit (4 * min a.val 3 + min b.val 3) &&
      decide (a.val < 3) && decide (b.val < 3)) = (854 : ℕ).testBit (4 * a.val + b.val) := by
    decide
  exact key u v

theorem lower (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) : ¬ RepSizeAtMost (A0 n m) (n + m) := by
  intro h
  set R : Finset (Fin n) := Finset.univ.filter (fun a : Fin n => a.val < 3) with hR
  set K : Finset (Fin m) := Finset.univ.filter (fun b : Fin m => b.val < 3) with hK
  have diag : ∀ i : ℕ, i < 3 → (64478 : Nat).testBit (4 * min i 3 + min i 3) = false := by
    intro i hi; interval_cases i <;> decide
  have c1 : ∀ u ∈ R, ∃ v ∈ K, A0 n m u v = false := by
    intro u hu
    simp [hR] at hu
    refine ⟨⟨u.val, by omega⟩, by simp [hK]; exact hu, ?_⟩
    simp only [A0]; exact diag u.val hu
  have c2 : ∀ v ∈ K, ∃ u ∈ R, A0 n m u v = false := by
    intro v hv
    simp [hK] at hv
    refine ⟨⟨v.val, by omega⟩, by simp [hR]; exact hv, ?_⟩
    simp only [A0]; exact diag v.val hv
  have c3 : ∃ u ∈ R, ∃ v ∈ K, A0 n m u v = true :=
    ⟨⟨0, by omega⟩, by simp [hR], ⟨1, by omega⟩, by simp [hK], by simp [A0]; decide⟩
  obtain ⟨s', hs', hle⟩ := RepInduced.induced n m (n + m) (A0 n m) R K c1 c2 c3 h
  have rows : (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A0 n m a b = true ∧
      ∃ a' : Fin n, A0 n m a' b = false)).card = n := by
    rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
    intro a _
    by_cases ha : a.val = 0
    · refine ⟨⟨1, by omega⟩, ?_, ⟨1, by omega⟩, ?_⟩
      · simp only [A0, ha]; decide
      · simp only [A0]; decide
    · refine ⟨⟨0, by omega⟩, ?_, ⟨0, by omega⟩, ?_⟩
      · simp only [A0]
        have : min a.val 3 = 1 ∨ min a.val 3 = 2 ∨ min a.val 3 = 3 := by omega
        rcases this with h | h | h <;> rw [h] <;> decide
      · simp only [A0]; decide
  have cols : (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A0 n m a b = true ∧
      ∃ b' : Fin m, A0 n m a b' = false)).card = m := by
    rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
    intro b _
    by_cases hb : b.val = 0
    · refine ⟨⟨1, by omega⟩, ?_, ⟨1, by omega⟩, ?_⟩
      · simp only [A0, hb]; decide
      · simp only [A0]; decide
    · refine ⟨⟨0, by omega⟩, ?_, ⟨0, by omega⟩, ?_⟩
      · simp only [A0]
        have : min b.val 3 = 1 ∨ min b.val 3 = 2 ∨ min b.val 3 = 3 := by omega
        rcases this with h | h | h <;> rw [h] <;> decide
      · simp only [A0]; decide
  have cR : R.card ≤ 3 := by
    calc R.card ≤ (Finset.range 3).card := by
          apply Finset.card_le_card_of_injOn (fun a : Fin n => a.val)
          · intro a ha; simp [hR] at ha; simpa using ha
          · intro a _ b _ e; exact Fin.ext e
      _ = 3 := by simp
  have cK : K.card ≤ 3 := by
    calc K.card ≤ (Finset.range 3).card := by
          apply Finset.card_le_card_of_injOn (fun a : Fin m => a.val)
          · intro a ha; simp [hK] at ha; simpa using ha
          · intro a _ b _ e; exact Fin.ext e
      _ = 3 := by simp
  have f1 := Finset.card_filter_le R (fun a => ∃ b ∈ K, A0 n m a b = true)
  have f2 := Finset.card_filter_le K (fun b => ∃ a ∈ R, A0 n m a b = true)
  rw [rows, cols] at hle
  exact core_lower n m hn hm s' (by omega) hs'

end PEqualNP.Outside.L_meta_27804
namespace PEqualNP.Outside.L_meta_27804

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_27804.Helpers PEqualNP.Outside.L_meta_27804.RepReads

def chain : ℕ → List ℕ → List Gate
  | _, [] => []
  | b, w :: ws => ⟨GateOp.or, [b, w]⟩ :: chain (b + 1) ws

theorem chain_length (b : ℕ) (ws : List ℕ) : (chain b ws).length = ws.length := by
  induction ws generalizing b with
  | nil => rfl
  | cons w ws ih => simp [chain, ih]

theorem chain_ok (b : ℕ) (ws : List ℕ) :
    ∀ g ∈ chain b ws, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction ws generalizing b with
  | nil => simp [chain]
  | cons w ws ih =>
    intro g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp
    · exact ih (b + 1) g hg

theorem chain_val (ws : List ℕ) : ∀ (b : ℕ) (W : List Bool), W.length = b + 1 →
    (∀ w ∈ ws, w < W.length) →
    (wiresFrom (chain b ws) W).getD (b + ws.length) false =
      (W.getD b false || ws.any fun w => W.getD w false) := by
  induction ws with
  | nil => intro b W _ _; simp [chain, wiresFrom]
  | cons w ws ih =>
    intro b W hl hw
    have step : wiresFrom (chain b (w :: ws)) W = wiresFrom (chain (b + 1) ws)
        (W ++ [GateOp.or.eval ([b, w].map fun i => W.getD i false)]) := rfl
    rw [step]
    have hw' : ∀ x ∈ ws, x < (W ++ [GateOp.or.eval ([b, w].map fun i => W.getD i false)]).length := by
      intro x hx; simp; have := hw x (by simp [hx]); omega
    have e : b + (w :: ws).length = b + 1 + ws.length := by simp; omega
    rw [e, ih (b + 1) _ (by simp [hl]) hw']
    have hb : (W ++ [GateOp.or.eval ([b, w].map fun i => W.getD i false)]).getD (b + 1) false =
        (W.getD b false || W.getD w false) := by
      rw [getD_snoc, if_pos (by omega)]; simp [GateOp.eval]
    rw [hb]
    have hrest : (ws.any fun x => (W ++ [GateOp.or.eval ([b, w].map fun i => W.getD i false)]).getD x false)
        = ws.any fun x => W.getD x false := by
      have pt : ∀ x ∈ ws, (W ++ [GateOp.or.eval ([b, w].map fun i => W.getD i false)]).getD x false
          = W.getD x false := by
        intro x hx
        rw [getD_snoc, if_neg (by have := hw x (by simp [hx]); omega)]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨x, hx, h⟩; exact ⟨x, hx, by rw [← pt x hx]; exact h⟩
      · rintro ⟨x, hx, h⟩; exact ⟨x, hx, by rw [pt x hx]; exact h⟩
    rw [hrest]
    simp [Bool.or_assoc]

theorem getD_app (V t : List Bool) (i : ℕ) : (V ++ t).getD i false =
    if i < V.length then V.getD i false else t.getD (i - V.length) false := by
  split_ifs with h
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_append_right _ _ _ _ (by omega)]

def pre (n m : ℕ) : List Gate :=
  [⟨GateOp.or, [0, n]⟩, ⟨GateOp.or, [1, n + 1]⟩, ⟨GateOp.or, [2, n + 2]⟩,
   ⟨GateOp.and, [n + m, n + m + 1]⟩, ⟨GateOp.or, [n + m, n + m + 1]⟩,
   ⟨GateOp.and, [n + m + 4, n + m + 2]⟩, ⟨GateOp.or, [n + m + 3, n + m + 5]⟩]

def extras (n m : ℕ) : List ℕ :=
  (List.range (n - 3)).map (· + 3) ++ (List.range (m - 3)).map (fun j => n + 3 + j)

def upperC (n m : ℕ) : Circuit :=
  ⟨pre n m ++ chain (n + m + 6) (extras n m), n + m + 6 + (extras n m).length⟩

theorem pre_val (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) (W : List Bool) (hl : W.length = n + m) :
    (wiresFrom (pre n m) W).getD (n + m + 6) false =
      (((W.getD 0 false || W.getD n false) && (W.getD 1 false || W.getD (n + 1) false)) ||
       ((W.getD 0 false || W.getD n false) || (W.getD 1 false || W.getD (n + 1) false)) &&
         (W.getD 2 false || W.getD (n + 2) false)) := by
  simp only [wiresFrom, pre, List.foldl, getD_app, List.length_append, List.length_singleton, hl,
    List.map, GateOp.eval]
  simp (disch := omega) only [if_pos, if_neg, Nat.sub_self, List.getD_cons_zero]
  simp [List.all, List.any, Bool.and_comm]

theorem pre_length (n m : ℕ) : (pre n m).length = 7 := rfl

theorem extras_length (n m : ℕ) : (extras n m).length = n - 3 + (m - 3) := by
  simp [extras]

theorem upper_size (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) : (upperC n m).size ≤ n + m + 1 := by
  simp only [upperC, Circuit.size, List.length_append, pre_length, chain_length, extras_length]
  omega

theorem upper_mono (n m : ℕ) : Monotone2 (upperC n m) := by
  intro g hg
  simp only [upperC, List.mem_append] at hg
  rcases hg with hg | hg
  · simp only [pre, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exact chain_ok _ _ g hg

theorem extras_any (n m : ℕ) (hn : 4 ≤ n) (u v : ℕ) (hu : u < n) (hv : v < m) :
    ((extras n m).any fun w => (inp (n + m) {u, n + v}).getD w false) =
      decide (3 ≤ u ∨ 3 ≤ v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, inp_getD, decide_eq_true_eq, extras, List.mem_append, List.mem_map,
    List.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨w, hw, h⟩
    rcases hw with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;> omega
  · intro h
    by_cases h3 : 3 ≤ u
    · exact ⟨u, Or.inl ⟨u - 3, by omega, by omega⟩, by omega⟩
    · exact ⟨n + v, Or.inr ⟨v - 3, by omega, by omega⟩, by omega⟩

theorem upper_rep (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) : Represents (A0 n m) (upperC n m) := by
  intro u v
  have hu := u.2
  have hv := v.2
  rw [oneEach_eq]
  set W := inp (n + m) {(u : ℕ), n + (v : ℕ)} with hW
  have hl : W.length = n + m := by simp [hW, inp]
  unfold Circuit.eval
  rw [wires_eq]
  simp only [upperC]
  rw [wiresFrom_append]
  have hlen : (wiresFrom (pre n m) W).length = n + m + 6 + 1 := by
    rw [length_wiresFrom, hl, pre_length]
  have ws_lt : ∀ w ∈ extras n m, w < (wiresFrom (pre n m) W).length := by
    intro w hw
    rw [hlen]
    simp only [extras, List.mem_append, List.mem_map, List.mem_range] at hw
    rcases hw with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;> omega
  rw [chain_val _ _ _ hlen ws_lt, pre_val n m hn hm W hl]
  have hany : ((extras n m).any fun w => (wiresFrom (pre n m) W).getD w false) =
      ((extras n m).any fun w => W.getD w false) := by
    have pt : ∀ w ∈ extras n m, (wiresFrom (pre n m) W).getD w false = W.getD w false := by
      intro w hw
      apply getD_wiresFrom
      rw [hl]
      simp only [extras, List.mem_append, List.mem_map, List.mem_range] at hw
      rcases hw with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;> omega
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, by rw [← pt x hx]; exact h⟩
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, by rw [pt x hx]; exact h⟩
  rw [hany, hW, extras_any n m hn u v hu hv]
  have p : ∀ i : ℕ, i < 3 → ((inp (n + m) {(u : ℕ), n + (v : ℕ)}).getD i false ||
      (inp (n + m) {(u : ℕ), n + (v : ℕ)}).getD (n + i) false) = decide ((u : ℕ) = i ∨ (v : ℕ) = i) := by
    intro i hi
    apply Bool.eq_iff_iff.mpr
    simp only [inp_getD, Finset.mem_insert, Finset.mem_singleton, Bool.or_eq_true,
      decide_eq_true_eq]
    omega
  have p0 := p 0 (by omega)
  rw [Nat.add_zero] at p0
  rw [p0, p 1 (by omega), p 2 (by omega)]
  unfold A0
  by_cases big : 3 ≤ (u : ℕ) ∨ 3 ≤ (v : ℕ)
  · rw [decide_eq_true big, Bool.or_true]
    have ha : min (u : ℕ) 3 ≤ 3 := min_le_right _ _
    have hb : min (v : ℕ) 3 ≤ 3 := min_le_right _ _
    have hab : min (u : ℕ) 3 = 3 ∨ min (v : ℕ) 3 = 3 := by omega
    generalize min (u : ℕ) 3 = a at ha hab
    generalize min (v : ℕ) 3 = b at hb hab
    symm
    interval_cases a <;> interval_cases b <;> first | omega | decide
  · have h1 : (u : ℕ) < 3 := by omega
    have h2 : (v : ℕ) < 3 := by omega
    have e1 : min (u : ℕ) 3 = u := by omega
    have e2 : min (v : ℕ) 3 = v := by omega
    rw [decide_eq_false big, e1, e2]
    generalize (u : ℕ) = a at h1
    generalize (v : ℕ) = b at h2
    interval_cases a <;> interval_cases b <;> decide

end PEqualNP.Outside.L_meta_27804
theorem PEqualNP.Outside.L_meta_27804 : (∀ (n m : Nat), 4 ≤ n → 4 ≤ m →
  let A := fun (u : Fin n) (v : Fin m) =>
    (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)
  PEqualNP.Represents.RepSizeAtMost A (n + m + 1) ∧
    ¬ PEqualNP.Represents.RepSizeAtMost A (n + m)) := by
  intro n m hn hm
  exact ⟨⟨PEqualNP.Outside.L_meta_27804.upperC n m, PEqualNP.Outside.L_meta_27804.upper_mono n m,
    PEqualNP.Outside.L_meta_27804.upper_size n m hn hm,
    PEqualNP.Outside.L_meta_27804.upper_rep n m hn hm⟩,
    PEqualNP.Outside.L_meta_27804.lower n m hn hm⟩
