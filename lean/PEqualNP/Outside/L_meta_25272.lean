import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25272 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147517 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.not, [8]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [13, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
