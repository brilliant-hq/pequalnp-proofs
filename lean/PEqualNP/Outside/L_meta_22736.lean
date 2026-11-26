import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22736 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1899642 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 21]⟩], 23⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
