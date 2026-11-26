import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22427 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17945 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.not, [1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [2, 5]⟩, ⟨.not, [8]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.not, [0]⟩, ⟨.and, [10, 13]⟩, ⟨.and, [6, 14]⟩, ⟨.not, [12]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [15, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
