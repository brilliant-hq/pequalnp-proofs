import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22952 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (908215 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 24]⟩], 25⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
