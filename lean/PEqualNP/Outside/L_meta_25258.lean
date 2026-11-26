import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25258 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50847 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.not, [5]⟩, ⟨.not, [7]⟩, ⟨.or, [6, 8]⟩, ⟨.not, [8]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [9, 13]⟩, ⟨.and, [11, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
