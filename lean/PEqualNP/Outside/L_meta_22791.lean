import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22791 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4028141 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 22]⟩], 23⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
