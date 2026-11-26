import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23886 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12760 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.not, [6]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.and, [5, 8]⟩,
    ⟨.or, [9, 10]⟩
  ], 11⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
