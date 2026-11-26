import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19982 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14991291321697978680 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [24, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [34, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 41]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
