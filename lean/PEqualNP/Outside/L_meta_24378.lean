import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24378 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (816041919 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [4, 6]⟩, ⟨.not, [7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [9, 11]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
