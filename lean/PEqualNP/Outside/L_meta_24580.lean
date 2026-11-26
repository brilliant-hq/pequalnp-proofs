import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24580 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6442943 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [2, 3]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [9, 10]⟩,
    ⟨.not, [11]⟩,
    ⟨.and, [8, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
