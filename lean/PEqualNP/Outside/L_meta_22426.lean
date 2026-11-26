import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22426 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17336 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [0, 3]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [8, 10]⟩, ⟨.and, [5, 9]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [0, 14]⟩, ⟨.or, [4, 16]⟩, ⟨.not, [17]⟩, ⟨.or, [15, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
