import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22684 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843130 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 22]⟩], 23⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
