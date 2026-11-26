import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22704 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (903149 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 22]⟩], 23⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
