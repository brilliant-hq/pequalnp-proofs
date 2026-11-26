import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22646 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (817020 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 22]⟩], 23⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
