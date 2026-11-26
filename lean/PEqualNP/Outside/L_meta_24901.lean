import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24901 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2330299 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [0, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [9, 10]⟩, ⟨.not, [11]⟩, ⟨.or, [12, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
