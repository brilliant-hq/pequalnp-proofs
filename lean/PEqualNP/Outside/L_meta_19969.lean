import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19969 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11683908189968026665 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [34, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [31, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [30, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 40]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
