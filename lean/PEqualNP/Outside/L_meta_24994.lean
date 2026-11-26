import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24994 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549403 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.and, [3, 4]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.and, [1, 7]⟩,
    ⟨.and, [2, 8]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.or, [6, 9]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.not, [13]⟩
  ], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
