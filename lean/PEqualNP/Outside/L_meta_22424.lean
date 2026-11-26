import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22424 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17076 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [1, 3]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.not, [11]⟩, ⟨.and, [2, 12]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [1, 14]⟩, ⟨.and, [6, 12]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [14, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
