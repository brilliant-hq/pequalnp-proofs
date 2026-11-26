import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22896 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940214 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 23]⟩], 24⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
