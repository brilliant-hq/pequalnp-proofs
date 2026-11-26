import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19132 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => !(decide (u = 0) && decide (v = 0))) 7 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 9] }], output := 16 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
