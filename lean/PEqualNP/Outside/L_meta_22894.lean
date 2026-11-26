import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22894 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940149 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 20]⟩], 24⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
