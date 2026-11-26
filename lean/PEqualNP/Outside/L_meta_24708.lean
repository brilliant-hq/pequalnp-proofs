import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24708 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16927 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.not, [0]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [4, 8]⟩,
    ⟨.and, [6, 9]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.not, [11]⟩,
    ⟨.or, [7, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
