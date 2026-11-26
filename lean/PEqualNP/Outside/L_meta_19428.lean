import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19428 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24894758 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide
