import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25963 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([11, 7, 3, 0] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨⟨[⟨.not, [3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [8, 9]⟩,
    ⟨.or, [0, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [11, 12]⟩,
    ⟨.or, [10, 13]⟩], 14⟩, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
  · decide
