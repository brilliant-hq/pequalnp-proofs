import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19951 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6992850275190006930 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [28, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [32, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [38, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 41]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
