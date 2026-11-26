import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22256 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816953 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 18]⟩], 22⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
