import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23455 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2149823 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.not, [6]⟩,
    ⟨.and, [8, 9]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.not, [11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
