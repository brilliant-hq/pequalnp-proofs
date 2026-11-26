import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23386 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (116415 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.and, [1, 2]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.not, [7]⟩,
    ⟨.and, [1, 8]⟩,
    ⟨.and, [2, 8]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.or, [10, 11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
