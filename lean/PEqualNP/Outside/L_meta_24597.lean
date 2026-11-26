import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24597 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270582957 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.not, [0]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.and, [8, 9]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.not, [12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
