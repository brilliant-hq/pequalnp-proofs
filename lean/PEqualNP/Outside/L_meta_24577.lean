import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24577 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6377407 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [8, 10]⟩,
    ⟨.or, [6, 11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
