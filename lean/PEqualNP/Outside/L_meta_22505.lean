import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22505 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898221 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 19]⟩], 22⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
