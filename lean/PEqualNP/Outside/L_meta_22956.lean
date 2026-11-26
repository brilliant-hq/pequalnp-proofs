import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22956 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940410 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 12]⟩], 25⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
