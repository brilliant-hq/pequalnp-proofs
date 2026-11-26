import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22068 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16575 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.not, [0]⟩,
    ⟨.and, [3, 6]⟩,
    ⟨.not, [0]⟩,
    ⟨.and, [4, 8]⟩,
    ⟨.not, [0]⟩,
    ⟨.and, [5, 10]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [13, 11]⟩,
    ⟨.or, [14, 12]⟩,
    ⟨.not, [15]⟩
  ], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
