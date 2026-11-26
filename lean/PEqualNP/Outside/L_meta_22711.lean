import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22711 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (908150 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 20]⟩], 23⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
