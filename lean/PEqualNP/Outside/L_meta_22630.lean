import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22630 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (327098 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 22]⟩], 23⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
