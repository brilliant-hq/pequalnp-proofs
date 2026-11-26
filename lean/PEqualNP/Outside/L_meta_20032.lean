import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20032 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5928307661352831525 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [27, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [30, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [24, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [26, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [37, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 41]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
