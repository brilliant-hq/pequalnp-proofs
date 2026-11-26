import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19980 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3033546467241018405 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [26, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [40, 41]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
