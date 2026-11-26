import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24898 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2313915 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.and, [2, 7]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.not, [8]⟩,
    ⟨.not, [9]⟩,
    ⟨.or, [6, 11]⟩,
    ⟨.or, [2, 12]⟩,
    ⟨.and, [10, 13]⟩
  ], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
