import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19960 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8109965352779728530 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [28, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [29, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [41, 40]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
