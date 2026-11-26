import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22136 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33713 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.not, [7]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [10, 5]⟩, ⟨.not, [11]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [15, 14]⟩], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
