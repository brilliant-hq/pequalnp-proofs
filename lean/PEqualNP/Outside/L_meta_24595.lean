import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24595 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270582705 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.not, [5]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [1, 9]⟩,
    ⟨.and, [6, 10]⟩,
    ⟨.not, [11]⟩,
    ⟨.and, [8, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
