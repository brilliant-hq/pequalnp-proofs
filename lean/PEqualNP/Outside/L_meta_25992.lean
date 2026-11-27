import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25992 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 14, 3, 1] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨⟨[⟨.or, [3, 2]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [10, 9]⟩, ⟨.or, [8, 4]⟩, ⟨.not, [12]⟩, ⟨.or, [13, 11]⟩], 14⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    fin_cases hg <;> exact ⟨by simp, by decide⟩
  · decide
  · decide
  · decide
