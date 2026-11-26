import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19990 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6099045440807847450 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [26, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [33, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [35, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [36, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [42, 34]⟩], 43⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
