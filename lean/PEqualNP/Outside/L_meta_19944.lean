import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19944 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9599430892109718240 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [31, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [32, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [27, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 35]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
