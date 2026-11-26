import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24774 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (118328 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 1]⟩,
      ⟨.or, [6, 5]⟩,
      ⟨.not, [7]⟩,
      ⟨.and, [2, 8]⟩,
      ⟨.or, [3, 4]⟩,
      ⟨.or, [10, 5]⟩,
      ⟨.and, [6, 11]⟩,
      ⟨.or, [9, 12]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
