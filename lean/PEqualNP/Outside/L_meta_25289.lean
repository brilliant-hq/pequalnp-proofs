import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25289 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2149424 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
        ⟨.or, [0, 1]⟩,
        ⟨.or, [4, 6]⟩,
        ⟨.or, [5, 7]⟩,
        ⟨.not, [8]⟩,
        ⟨.and, [3, 9]⟩,
        ⟨.and, [2, 9]⟩,
        ⟨.or, [4, 5]⟩,
        ⟨.and, [6, 12]⟩,
        ⟨.or, [10, 13]⟩,
        ⟨.or, [11, 14]⟩
      ], 15⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
