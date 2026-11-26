import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24081 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (279453 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [2, 4]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [1, 6]⟩, ⟨.not, [7]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [5, 12]⟩], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
