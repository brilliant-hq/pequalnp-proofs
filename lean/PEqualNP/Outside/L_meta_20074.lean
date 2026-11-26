import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20074 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10108984885455782700 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 41]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
