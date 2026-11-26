import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24588 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549401 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [3, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [5, 11]⟩, ⟨.not, [12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
