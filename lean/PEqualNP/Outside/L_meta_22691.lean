import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22691 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843198 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 21]⟩], 23⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
