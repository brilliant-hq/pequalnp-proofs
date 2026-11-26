import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21727 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4190 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.not, [5]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [4, 9]⟩, ⟨.not, [8]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [7, 15]⟩], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
