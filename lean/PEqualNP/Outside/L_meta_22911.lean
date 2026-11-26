import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22911 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (414 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [2, 3]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.and, [1, 5]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.and, [8, 9]⟩
  ], 10⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
