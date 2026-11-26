import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21711 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275166 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.not, [1]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [2, 4]⟩, ⟨.not, [3]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [10, 11]⟩, ⟨.not, [9]⟩, ⟨.or, [0, 13]⟩, ⟨.and, [12, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
