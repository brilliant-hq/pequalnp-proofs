import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22429 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17978 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 4]⟩, ⟨.not, [6]⟩, ⟨.or, [3, 7]⟩, ⟨.not, [9]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [8, 10]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [14, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
