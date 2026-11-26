import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24806 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147372 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [1, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [6, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
