import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19048 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4459 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
