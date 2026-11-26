import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19947 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9901191629971542690 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [24, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [29, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 41]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
