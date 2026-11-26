import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22674 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841661 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 21]⟩], 23⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
