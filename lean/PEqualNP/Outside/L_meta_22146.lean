import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22146 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33982 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [3, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [0, 1]⟩, ⟨.not, [7]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [11, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
