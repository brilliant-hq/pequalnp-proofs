import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19133 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => !(decide (u = 0) && decide (v = 0))) 9 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 11] }], output := 20 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
