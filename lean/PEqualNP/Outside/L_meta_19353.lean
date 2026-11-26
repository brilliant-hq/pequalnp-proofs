import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19353 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16223868 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [13, 2]⟩, ⟨.and, [11, 14]⟩, ⟨.or, [13, 11]⟩, ⟨.not, [15]⟩, ⟨.and, [16, 17]⟩], 18⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
