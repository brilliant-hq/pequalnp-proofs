import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18681_aux

open PEqualNP.CircuitLowerBounds

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

end PEqualNP.Outside.L_meta_18681_aux

open PEqualNP.Outside.L_meta_18681_aux in
theorem PEqualNP.Outside.L_meta_18681 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 ∈ x2.gates, x6.inputs.Nodup) → x3 < x1 + x2.size → x4 < x1 + x2.size → x3 ≠ x4 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), x10.size = x2.size + (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 x1 x10 ∧ (∀ x11 ∈ x10.gates, x11.inputs.Nodup) ∧ ∀ (x11 : Fin x1 → Bool), (∀ x12 < x1 + x2.size, PEqualNP.BlindGate.wireValue x10 x1 x11 x12 = PEqualNP.BlindGate.wireValue x2 x1 x11 x12) ∧ PEqualNP.BlindGate.wireValue x10 x1 x11 (x1 + x2.size) = (PEqualNP.BlindGate.wireValue x2 x1 x11 x3 || PEqualNP.BlindGate.wireValue x2 x1 x11 x4) := by
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
