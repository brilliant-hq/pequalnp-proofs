import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19397 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (12064434 : ℕ).testBit (5 * u.val + v.val)) 13) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [11, 9]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [16, 8]⟩, ⟨.and, [4, 17]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [21, 19]⟩], 22⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
