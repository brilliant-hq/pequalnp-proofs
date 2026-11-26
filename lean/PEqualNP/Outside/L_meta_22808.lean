import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22808 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34719 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [8, 0]⟩, ⟨.and, [9, 6]⟩], 10⟩, ?_, ?_, ?_⟩
  · intro g hg
    fin_cases hg <;> exact ⟨by simp, by decide⟩
  · decide
  · decide
