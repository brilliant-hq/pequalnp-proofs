import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_20849 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (25364513 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 17] }], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
