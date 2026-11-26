import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22993 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (1838 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [2, 3]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [1, 7]⟩,
    ⟨.or, [1, 8]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.or, [9, 11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
