import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22542 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940205 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 21]⟩], 22⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
