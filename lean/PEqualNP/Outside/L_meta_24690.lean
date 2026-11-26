import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24690 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (393 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.and, [7, 8]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.not, [11]⟩,
    ⟨.and, [6, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
