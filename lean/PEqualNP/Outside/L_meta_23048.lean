import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23048 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (3902 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [2, 5]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [1, 7]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.and, [3, 8]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.or, [0, 12]⟩,
    ⟨.and, [9, 13]⟩
  ], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
