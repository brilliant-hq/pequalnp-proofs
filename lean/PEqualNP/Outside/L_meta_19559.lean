import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_19559 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577402 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }], output := 18 }, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> (subst h; simp)
  · decide
  · decide
