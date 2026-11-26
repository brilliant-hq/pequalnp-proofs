import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24892 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2215611 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.not, [2]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.not, [10]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
