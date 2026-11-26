import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22656 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841135 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 17]⟩], 23⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
