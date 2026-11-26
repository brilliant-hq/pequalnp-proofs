import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19614 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3574717 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 17]⟩], 18⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
