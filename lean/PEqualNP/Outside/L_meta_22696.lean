import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22696 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849788 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 22]⟩], 23⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
