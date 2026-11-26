import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19978 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5360062095110517900 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [31, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [29, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 40]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
