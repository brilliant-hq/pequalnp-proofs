import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22872 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883510 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 23]⟩], 24⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
