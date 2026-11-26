import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20034 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5346231350888391705 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [32, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [35, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [33, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 42]⟩], 43⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
