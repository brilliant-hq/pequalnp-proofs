import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25158 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16794 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [3, 4]⟩,
      ⟨.or, [1, 6]⟩,
      ⟨.and, [0, 7]⟩,
      ⟨.or, [5, 6]⟩,
      ⟨.or, [0, 9]⟩,
      ⟨.not, [10]⟩,
      ⟨.or, [8, 11]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
