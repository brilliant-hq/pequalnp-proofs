import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22829 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841718 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 19]⟩], 24⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
