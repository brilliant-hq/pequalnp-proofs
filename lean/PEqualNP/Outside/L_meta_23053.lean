import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_23053 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1949310 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 24]⟩], 25⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
