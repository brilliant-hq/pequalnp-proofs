import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24706 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16917 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.not, [4]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.or, [3, 5]⟩,
    ⟨.or, [1, 9]⟩,
    ⟨.not, [10]⟩,
    ⟨.and, [7, 11]⟩,
    ⟨.or, [8, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
