import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24707 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16919 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.and, [1, 3]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.and, [7, 8]⟩,
    ⟨.not, [10]⟩,
    ⟨.or, [11, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
