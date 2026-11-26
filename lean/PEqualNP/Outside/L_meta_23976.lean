import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23976 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧
        ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
          (12631 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [1, 2]⟩,
      ⟨.or, [1, 2]⟩,
      ⟨.not, [3]⟩,
      ⟨.or, [6, 7]⟩,
      ⟨.or, [4, 5]⟩,
      ⟨.not, [9]⟩,
      ⟨.or, [0, 10]⟩,
      ⟨.and, [8, 11]⟩], 12⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
