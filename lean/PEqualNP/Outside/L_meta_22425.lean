import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22425 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17086 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [3, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.not, [7]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.not, [13]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [0, 15]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [14, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
