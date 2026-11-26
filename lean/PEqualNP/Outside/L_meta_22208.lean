import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22208 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843710 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 20]⟩], 21⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
