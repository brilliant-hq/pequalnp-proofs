import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25280 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147765 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [4, 6]⟩, ⟨.not, [6]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [7, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.not, [14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
