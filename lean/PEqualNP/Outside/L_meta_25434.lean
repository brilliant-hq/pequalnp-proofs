import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25434 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549385 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.not, [0]⟩,
      ⟨.or, [1, 2]⟩,
      ⟨.and, [7, 4]⟩,
      ⟨.or, [8, 3]⟩,
      ⟨.or, [7, 4]⟩,
      ⟨.or, [0, 9]⟩,
      ⟨.and, [11, 10]⟩,
      ⟨.or, [12, 5]⟩,
      ⟨.not, [13]⟩], 14⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
