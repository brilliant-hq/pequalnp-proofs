import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21717 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283481 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [0, 2]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [7, 10]⟩, ⟨.not, [11]⟩, ⟨.not, [4]⟩, ⟨.or, [9, 13]⟩, ⟨.and, [12, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
