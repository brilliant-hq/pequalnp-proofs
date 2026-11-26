import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20060 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5918728716082980945 : ℕ).testBit (8 * u.val + v.val)) 26 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [29, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [27, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [35, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [26, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 39]⟩], 41⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
