import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19967 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10678392892249613865 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [26, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [28, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [37, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 29]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
