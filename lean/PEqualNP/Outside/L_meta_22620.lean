import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22620 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17047 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [4, 5]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.and, [0, 4]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.not, [11]⟩,
    ⟨.or, [12, 13]⟩
  ], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
