import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22730 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883453 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 15]⟩], 23⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
