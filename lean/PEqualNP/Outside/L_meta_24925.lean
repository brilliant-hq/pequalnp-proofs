import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24925 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4310951 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.not, [5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.not, [11]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [10, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
