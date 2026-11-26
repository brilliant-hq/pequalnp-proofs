import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22244 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808954 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 20]⟩], 22⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
