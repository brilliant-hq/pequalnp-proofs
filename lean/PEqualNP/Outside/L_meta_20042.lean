import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20042 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7093347072485314830 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [27, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [33, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [23, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 21]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
