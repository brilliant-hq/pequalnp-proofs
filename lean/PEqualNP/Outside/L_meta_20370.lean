import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20370 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8398537473870936615 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [34, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [33, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [32, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [42, 40]⟩], 43⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
