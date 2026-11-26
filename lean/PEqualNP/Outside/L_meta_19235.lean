import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19235 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 4 => (123 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [6]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [7]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 10]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 9]⟩], 12⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h <;> subst h <;>
      exact ⟨by simp, by decide⟩
  · decide
  · decide
