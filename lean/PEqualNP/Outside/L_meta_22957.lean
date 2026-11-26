import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22957 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940411 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [24, 22]⟩], 25⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
