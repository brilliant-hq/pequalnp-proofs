import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20005 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14466700110149527140 : ℕ).testBit (8 * u.val + v.val)) 26 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [33, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [31, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 36]⟩], 41⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
