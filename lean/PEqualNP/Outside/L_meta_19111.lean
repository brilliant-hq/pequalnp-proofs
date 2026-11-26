import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19111 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (15855 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [13] }], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
