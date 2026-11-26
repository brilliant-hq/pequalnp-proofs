import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25253 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50736 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [5, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [6, 0]⟩, ⟨.or, [6, 7]⟩, ⟨.not, [9]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [14, 8]⟩], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
