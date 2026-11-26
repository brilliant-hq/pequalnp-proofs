import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22463 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 15 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18089 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.and, [0, 1]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.and, [2, 8]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.or, [2, 8]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.and, [2, 11]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [14, 17]⟩,
    ⟨.not, [17]⟩,
    ⟨.and, [18, 19]⟩
  ], 20⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
