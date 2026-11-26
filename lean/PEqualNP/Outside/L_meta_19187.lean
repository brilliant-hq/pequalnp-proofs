import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19187 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (6126 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.or, [2, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [8, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [10, 13]⟩], 14⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
