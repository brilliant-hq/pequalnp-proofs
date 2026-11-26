import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24896 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2297407 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [3, 9]⟩,
    ⟨.or, [0, 10]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [11, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
