import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23973 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8917 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.and, [0, 1]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.and, [2, 7]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [5, 10]⟩,
    ⟨.or, [9, 11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
