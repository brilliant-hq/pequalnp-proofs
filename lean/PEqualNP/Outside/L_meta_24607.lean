import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24607 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270585011 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.and, [7, 8]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.not, [11]⟩,
    ⟨.or, [9, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
