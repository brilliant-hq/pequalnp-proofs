import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20000 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5496967495809117315 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [24, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [34, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [40, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 41]⟩], 43⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
