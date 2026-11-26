import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23031 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (99886 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [7, 9]⟩,
    ⟨.or, [3, 10]⟩,
    ⟨.and, [8, 11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
