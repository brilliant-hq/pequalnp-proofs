import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22194 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17075 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.not, [1]⟩,
    ⟨.and, [3, 6]⟩,
    ⟨.not, [0]⟩,
    ⟨.and, [4, 8]⟩,
    ⟨.not, [0]⟩,
    ⟨.and, [5, 10]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.and, [2, 12]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [14, 11]⟩,
    ⟨.or, [15, 13]⟩,
    ⟨.not, [16]⟩
  ], 17⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
