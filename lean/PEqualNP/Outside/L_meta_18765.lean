import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18765_aux

open PEqualNP.CircuitLowerBounds

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega


theorem fold_pre (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by rw [List.foldl_cons, ht, List.append_assoc]⟩

theorem inp (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin n → Bool) (v : Fin n) :
    PEqualNP.BlindGate.wireValue C n x v = x v := by
  unfold PEqualNP.BlindGate.wireValue PEqualNP.CircuitLowerBounds.Circuit.wires
  obtain ⟨t, ht⟩ := fold_pre C.gates (List.ofFn x)
  rw [ht, List.getD_append _ _ _ _ (by simp)]
  simp

theorem app1 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 ∈ x2.gates, x6.inputs.Nodup) → x3 < x1 + x2.size → x4 < x1 + x2.size → x3 ≠ x4 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), x10.size = x2.size + (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 x1 x10 ∧ (∀ x11 ∈ x10.gates, x11.inputs.Nodup) ∧ ∀ (x11 : Fin x1 → Bool), (∀ x12 < x1 + x2.size, PEqualNP.BlindGate.wireValue x10 x1 x11 x12 = PEqualNP.BlindGate.wireValue x2 x1 x11 x12) ∧ PEqualNP.BlindGate.wireValue x10 x1 x11 (x1 + x2.size) = (PEqualNP.BlindGate.wireValue x2 x1 x11 x3 || PEqualNP.BlindGate.wireValue x2 x1 x11 x4) := by
  intro n C a b hC hN ha hb hab
  obtain ⟨hA, hR, hL⟩ := hC
  refine ⟨{ gates := C.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] }], output := n + C.size }, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · unfold PEqualNP.CircuitLowerBounds.Circuit.size
    simp
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hA g hg
    · exact Or.inr rfl
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · have := hR j hj i
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt at this
      rw [List.getD_append _ _ _ _ hj] at hi
      exact this hi
    · subst hj
      rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
      simp at hi
      unfold PEqualNP.CircuitLowerBounds.Circuit.size at ha hb
      rcases hi with rfl | rfl <;> omega
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hL g hg
    · rfl
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hN g hg
    · simp [hab]
  · intro x
    have hl := fold_len C.gates (List.ofFn x)
    simp only [List.length_ofFn] at hl
    unfold PEqualNP.CircuitLowerBounds.Circuit.size at ha hb
    refine ⟨?_, ?_⟩
    · intro w hw
      unfold PEqualNP.BlindGate.wireValue PEqualNP.CircuitLowerBounds.Circuit.wires
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      unfold PEqualNP.CircuitLowerBounds.Circuit.size at hw
      rw [List.getD_append _ _ _ _ (by omega)]
    · unfold PEqualNP.BlindGate.wireValue PEqualNP.CircuitLowerBounds.Circuit.wires
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      unfold PEqualNP.CircuitLowerBounds.Circuit.size
      rw [List.getD_append_right _ _ _ _ (by omega)]
      rw [hl, Nat.sub_self]
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval]

end PEqualNP.Outside.L_meta_18765_aux

open PEqualNP.Outside.L_meta_18765_aux in
theorem PEqualNP.Outside.L_meta_18765 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) (x5 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x7 ∈ x2.gates, x7.inputs.Nodup) → x3 < x1 + x2.size → x4 < x1 + x2.size → x3 ≠ x4 → x3 ≠ ↑x5 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : ℕ) (x14 : ℕ), x12.size ≤ x2.size + (2 : ℕ) ∧ PEqualNP.TopForm.IsAO2 x1 x12 ∧ (∀ x15 ∈ x12.gates, x15.inputs.Nodup) ∧ x13 ≠ x14 ∧ x13 < x1 + x12.size ∧ x14 < x1 + x12.size ∧ ∀ (x15 : Fin x1 → Bool), PEqualNP.BlindGate.wireValue x12 x1 x15 x13 = (PEqualNP.BlindGate.wireValue x2 x1 x15 x3 || PEqualNP.BlindGate.wireValue x2 x1 x15 x4) ∧ PEqualNP.BlindGate.wireValue x12 x1 x15 x14 = (PEqualNP.BlindGate.wireValue x2 x1 x15 x3 || x15 x5) := by
  intro n C a b v hC hN ha hb hab hav
  obtain ⟨C1, hs1, hC1, hN1, hw1⟩ := app1 n C a b hC hN ha hb hab
  obtain ⟨C2, hs2, hC2, hN2, hw2⟩ := app1 n C1 a v hC1 hN1 (by omega) (by omega) hav
  refine ⟨C2, n + C.size, n + C1.size, by omega, hC2, hN2, by omega, by omega, by omega, fun x => ⟨?_, ?_⟩⟩
  · rw [(hw2 x).1 _ (by omega), (hw1 x).2]
  · rw [(hw2 x).2, (hw1 x).1 _ (by omega), inp]
