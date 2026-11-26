import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22692 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849709 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 22]⟩], 23⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
