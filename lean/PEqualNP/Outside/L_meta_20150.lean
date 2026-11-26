import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20150 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5515944280522376865 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [23, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [26, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [32, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [29, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 39]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
