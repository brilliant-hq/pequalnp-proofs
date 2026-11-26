import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20413 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (379 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 9]⟩], 12⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
