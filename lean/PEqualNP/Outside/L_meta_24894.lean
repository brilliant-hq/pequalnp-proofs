import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24894 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2215740 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.not, [5]⟩,
    ⟨.and, [2, 7]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [6, 9]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [3, 12]⟩,
    ⟨.or, [11, 13]⟩
  ], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
