import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24489 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2117047 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.and, [3, 7]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.not, [6]⟩,
    ⟨.and, [9, 10]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.not, [12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
