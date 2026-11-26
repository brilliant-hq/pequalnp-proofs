import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_23657 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275388 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 16]⟩], 20⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
