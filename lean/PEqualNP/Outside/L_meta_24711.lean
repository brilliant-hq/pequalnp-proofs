import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24711 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16950 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [1, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [3, 8]⟩, ⟨.not, [10]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
