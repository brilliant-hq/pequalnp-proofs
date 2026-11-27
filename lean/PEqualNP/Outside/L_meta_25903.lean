import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_25903 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8080454460742251720 : ℕ).testBit (8 * u.val + v.val)) 25 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [31, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [30, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [29, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [24, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 36]⟩], 40⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
