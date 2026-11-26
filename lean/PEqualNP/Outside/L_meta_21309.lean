import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_21309 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103766 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 18]⟩], 19⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
