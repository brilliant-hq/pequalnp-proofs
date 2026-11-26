import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20026 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (813692034574725510 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [29, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [33, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [28, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [37, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 35]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
