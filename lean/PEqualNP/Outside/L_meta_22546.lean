import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22546 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947499 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 21]⟩], 22⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
