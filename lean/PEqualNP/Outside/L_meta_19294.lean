import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19294 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16235582 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.not, [5]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [0, 1]⟩, ⟨.not, [13]⟩,
    ⟨.not, [9]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [17, 16]⟩], 18⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
