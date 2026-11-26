import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19196 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => decide (v.val = u.val ∨ v.val = (u.val + 1) % 6)) 16 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 26]⟩], 27⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

