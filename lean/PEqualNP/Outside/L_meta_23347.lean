import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23347 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50078 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [6, 10]⟩,
    ⟨.or, [9, 11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
