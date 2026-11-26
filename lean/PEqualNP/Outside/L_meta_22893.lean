import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22893 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1939375 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 23]⟩], 24⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
