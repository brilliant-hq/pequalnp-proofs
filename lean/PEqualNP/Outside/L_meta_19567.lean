import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19567 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3245886 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.or, [1, 5]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [7, 11]⟩, ⟨.and, [12, 14]⟩, ⟨.not, [15]⟩, ⟨.and, [13, 16]⟩], 17⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
