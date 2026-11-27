import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25961 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([7, 5, 3, 0] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨⟨[⟨.and, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [8, 9]⟩,
    ⟨.or, [7, 10]⟩, ⟨.or, [3, 11]⟩, ⟨.not, [12]⟩], 13⟩,
    ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
  · decide
