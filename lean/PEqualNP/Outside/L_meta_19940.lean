import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19940 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (838035264769107540 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [31, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [28, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 38]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
