import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23622_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ren (n k i : ℕ) : ℕ :=
  if i < n + k then i else i - 1

def renGate (n k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (ren n k)⟩

def renCircuit (n k : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (renGate n k), ren n k C.output⟩

def gstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Agree (n k : ℕ) (w w' : List Bool) : Prop :=
  w.length = w'.length + 1 ∧ n + k < w.length ∧
    ∀ i, i ≠ n + k → w'.getD (ren n k i) false = w.getD i false

theorem agree_fold (n k : ℕ) (gs : List Gate)
    (hskip : ∀ g ∈ gs, n + k ∉ g.inputs) :
    ∀ w w' : List Bool, Agree n k w w' →
      Agree n k (gs.foldl gstep w) ((gs.map (renGate n k)).foldl gstep w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' ⟨hlen, hnk, hget⟩
    have hg : n + k ∉ g.inputs := hskip g List.mem_cons_self
    have hrest : ∀ g' ∈ gs, n + k ∉ g'.inputs := fun g' hg' => hskip g' (List.mem_cons_of_mem _ hg')
    simp only [List.map_cons, List.foldl_cons]
    apply ih hrest
    have hval : (renGate n k g).op.eval ((renGate n k g).inputs.map fun i => w'.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [renGate, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hget i (fun heq => hg (heq ▸ hi))
    refine ⟨by simp [gstep, hlen], by simp [gstep]; omega, fun i hi => ?_⟩
    rcases lt_trichotomy i w.length with hlt | rfl | hgt
    · have hlt' : ren n k i < w'.length := by
        unfold ren; split_ifs <;> omega
      simp only [gstep, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hlt', List.getElem?_append_left hlt]
      simpa [List.getD_eq_getElem?_getD] using hget i hi
    · have hren : ren n k w.length = w'.length := by
        unfold ren; split_ifs <;> omega
      rw [hren]
      simp only [gstep, List.getD_eq_getElem?_getD,
        List.getElem?_append_right le_rfl, Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
      simpa [List.getD_eq_getElem?_getD] using hval
    · have hge' : w'.length + 1 ≤ ren n k i := by
        unfold ren; split_ifs <;> omega
      have hge : w.length + 1 ≤ i := by omega
      simp only [gstep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false =
      if hi : i < n then decide (u.val = i)
      else if hj : i < n + m then decide (v.val = i - n)
      else false := by
  simp only [oneEach, List.getD_eq_getElem?_getD]
  by_cases hi : i < n
  · rw [dif_pos hi, List.getElem?_append_left (by simp [hi])]
    simp [hi, Fin.ext_iff, eq_comm]
  · rw [dif_neg hi]
    by_cases hj : i < n + m
    · rw [dif_pos hj, List.getElem?_append_right (by simp; omega)]
      simp only [List.length_ofFn, List.getElem?_ofFn]
      have hsub : i - n < m := by omega
      simp [hsub, Fin.ext_iff, eq_comm]
    · rw [dif_neg hj, List.getElem?_eq_none (by simp; omega)]
      rfl

theorem succAbove_val {m : ℕ} (k : Fin (m + 1)) (v : Fin m) :
    (k.succAbove v).val = if v.val < k.val then v.val else v.val + 1 := by
  unfold Fin.succAbove
  split_ifs <;> simp_all [Fin.lt_def] <;> omega

theorem agree_oneEach {n m : ℕ} (k : Fin (m + 1)) (u : Fin n) (v : Fin m) :
    Agree n k.val (oneEach u (k.succAbove v)) (oneEach u v) := by
  refine ⟨by simp [oneEach]; omega, by simp [oneEach]; omega, fun i hi => ?_⟩
  rw [oneEach_getD, oneEach_getD, succAbove_val]
  unfold ren
  by_cases hlt : i < n + k.val
  · rw [if_pos hlt]
    by_cases hin : i < n
    · simp [hin]
    · have him : i < n + m := by omega
      have him1 : i < n + (m + 1) := by omega
      simp only [dif_neg hin, dif_pos him, dif_pos him1]
      rw [decide_eq_decide]
      split_ifs <;> omega
  · rw [if_neg hlt]
    have hgt : n + k.val < i := by omega
    have hin : ¬ i < n := by omega
    have hin' : ¬ i - 1 < n := by omega
    rw [dif_neg hin', dif_neg hin]
    by_cases him : i - 1 < n + m
    · have him1 : i < n + (m + 1) := by omega
      rw [dif_pos him, dif_pos him1]
      rw [decide_eq_decide]
      split_ifs <;> omega
    · have him1 : ¬ i < n + (m + 1) := by omega
      rw [dif_neg him, dif_neg him1]

theorem ren_eq_row {n k i : ℕ} (hi : i ≠ n + k) (u : Fin n) (h : ren n k i = u.val) :
    i = u.val := by
  unfold ren at h
  have hu := u.isLt
  split_ifs at h <;> omega

theorem ren_eq_col {n m : ℕ} (k : Fin (m + 1)) {i : ℕ} (hi : i ≠ n + k.val) (v : Fin m)
    (h : ren n k.val i = n + v.val) : i = n + (k.succAbove v).val := by
  rw [succAbove_val]
  unfold ren at h
  split_ifs at h <;> split_ifs <;> omega

end PEqualNP.Outside.L_meta_23622_aux

open PEqualNP.Outside.L_meta_23622_aux in
theorem PEqualNP.Outside.L_meta_23622 : ∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.Represents.Represents A C → (∀ g ∈ C.gates, n + k.val ∉ g.inputs) → C.output ≠ n + k.val → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, C'.size = C.size ∧ (PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.FanInTwo C') ∧ PEqualNP.Represents.Represents (fun u v => A u (k.succAbove v)) C' ∧ (∀ u : Fin n, ((∃ g ∈ C'.gates, u.val ∈ g.inputs) ∨ C'.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C'.gates, n + v.val ∈ g.inputs) ∨ C'.output = n + v.val) → ((∃ g ∈ C.gates, n + (k.succAbove v).val ∈ g.inputs) ∨ C.output = n + (k.succAbove v).val)) := by
  intro n m A k C hrep hskip hout
  refine ⟨renCircuit n k.val C, ?_, ?_, ?_, ?_, ?_⟩
  · simp [renCircuit, PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro hfan g hg
    simp only [renCircuit, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    simpa [renGate] using hfan g0 hg0
  · intro u v
    have hfold := agree_fold n k.val C.gates hskip _ _ (agree_oneEach k u v)
    change ((C.gates.map (renGate n k.val)).foldl gstep (PEqualNP.Represents.oneEach u v)).getD
      (ren n k.val C.output) false = A u (k.succAbove v)
    rw [hfold.2.2 C.output hout]
    exact hrep u (k.succAbove v)
  · intro u hu
    rcases hu with ⟨g', hg', hin⟩ | ho
    · simp only [renCircuit, List.mem_map] at hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      simp only [renGate, List.mem_map] at hin
      obtain ⟨i, hi, heq⟩ := hin
      have hne : i ≠ n + k.val := fun h => hskip g hg (h ▸ hi)
      left
      exact ⟨g, hg, ren_eq_row hne u heq ▸ hi⟩
    · right
      exact ren_eq_row hout u ho
  · intro v hv
    rcases hv with ⟨g', hg', hin⟩ | ho
    · simp only [renCircuit, List.mem_map] at hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      simp only [renGate, List.mem_map] at hin
      obtain ⟨i, hi, heq⟩ := hin
      have hne : i ≠ n + k.val := fun h => hskip g hg (h ▸ hi)
      left
      exact ⟨g, hg, ren_eq_col k hne v heq ▸ hi⟩
    · right
      exact ren_eq_col k hout v ho
