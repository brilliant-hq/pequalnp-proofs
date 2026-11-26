import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24586 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (14896575 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.and, [3, 6]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [8, 10]⟩
  ], 11⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
