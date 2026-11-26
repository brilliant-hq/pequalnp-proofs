import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24120 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266718 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [0, 4]⟩,
      ⟨.or,  [2, 3]⟩,
      ⟨.or,  [1, 6]⟩,
      ⟨.and, [2, 3]⟩,
      ⟨.or,  [4, 8]⟩,
      ⟨.not, [9]⟩,
      ⟨.and, [7, 10]⟩,
      ⟨.or,  [5, 11]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
