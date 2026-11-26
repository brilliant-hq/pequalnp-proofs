import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22259 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (818812 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 21]⟩], 22⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
