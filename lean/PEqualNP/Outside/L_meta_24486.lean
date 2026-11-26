import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24486 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2114991 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.and, [3, 6]⟩,
    ⟨.not, [4]⟩,
    ⟨.or, [1, 8]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.not, [10]⟩,
    ⟨.or, [0, 11]⟩,
    ⟨.and, [9, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
