import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22734 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898236 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 20]⟩], 23⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
