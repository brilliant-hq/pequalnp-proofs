import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19938 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4081470838034108865 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [26, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [27, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [30, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [23, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [41, 40]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
