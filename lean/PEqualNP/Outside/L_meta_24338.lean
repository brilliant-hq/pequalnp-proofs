import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24338 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270550975 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [3, 4]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.and, [2, 6]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.not, [10]⟩,
    ⟨.or, [0, 11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
