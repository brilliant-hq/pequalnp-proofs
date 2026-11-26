import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21718 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283549 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.and, [4, 5]⟩, ⟨.not, [1]⟩, ⟨.or, [2, 6]⟩, ⟨.not, [3]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [3, 7]⟩, ⟨.not, [11]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
