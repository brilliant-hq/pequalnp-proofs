import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24587 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549391 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.and, [4, 7]⟩,
    ⟨.or, [3, 9]⟩,
    ⟨.and, [8, 10]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.not, [12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
