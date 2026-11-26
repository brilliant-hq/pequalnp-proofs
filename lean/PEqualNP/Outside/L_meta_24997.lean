import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24997 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549909 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [2, 8]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.not, [12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
