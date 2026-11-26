import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22892 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1939371 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 23]⟩], 24⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
