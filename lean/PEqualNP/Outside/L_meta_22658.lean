import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22658 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841147 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 22]⟩], 23⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
