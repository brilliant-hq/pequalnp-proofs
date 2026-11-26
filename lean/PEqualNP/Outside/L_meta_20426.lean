import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20426 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (991 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 9]⟩], 12⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
