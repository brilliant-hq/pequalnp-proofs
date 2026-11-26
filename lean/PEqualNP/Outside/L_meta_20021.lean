import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20021 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4868853174714768465 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [34, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [33, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [32, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 41]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
