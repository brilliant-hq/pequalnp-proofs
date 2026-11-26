import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20322 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1125029453109683085 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [28, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [31, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [34, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [38, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 42]⟩], 43⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
