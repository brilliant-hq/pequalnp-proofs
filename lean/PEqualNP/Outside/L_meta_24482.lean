import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24482 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2114448 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.and, [2, 3]⟩,
    ⟨.and, [0, 4]⟩,
    ⟨.and, [2, 6]⟩,
    ⟨.or, [5, 8]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.not, [11]⟩,
    ⟨.or, [7, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
