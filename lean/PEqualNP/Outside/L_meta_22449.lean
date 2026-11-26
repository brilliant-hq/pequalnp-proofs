import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22449 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1882100 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 18]⟩], 22⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
