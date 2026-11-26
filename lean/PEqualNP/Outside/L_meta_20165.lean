import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20165 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10691974706225816370 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [33, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [28, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [27, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 38]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
