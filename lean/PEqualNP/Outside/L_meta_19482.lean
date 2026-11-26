import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19482 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3251479 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide
