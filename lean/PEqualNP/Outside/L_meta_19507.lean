import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19507 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16221393 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[
    ⟨.or, [3, 4]⟩,
    ⟨.or, [1, 9]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.or, [6, 13]⟩,
    ⟨.not, [11]⟩,
    ⟨.or, [7, 15]⟩,
    ⟨.or, [14, 16]⟩,
    ⟨.or, [5, 12]⟩,
    ⟨.and, [17, 18]⟩
  ], 19⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by simp, by decide⟩
  · intro u v
    revert u v
    decide
