import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24893 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2215615 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.not, [2]⟩,
    ⟨.and, [1, 6]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.and, [4, 6]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.or, [1, 10]⟩,
    ⟨.not, [11]⟩,
    ⟨.or, [8, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
