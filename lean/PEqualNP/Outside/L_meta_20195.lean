import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20195 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10678392892249613865 : ℕ).testBit (8 * u.val + v.val)) 24 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [26, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [30, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [24, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 38]⟩], 39⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
