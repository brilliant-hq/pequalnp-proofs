import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22562 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948405 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 4]⟩], 22⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
