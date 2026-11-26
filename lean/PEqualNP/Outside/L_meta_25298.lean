import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25298 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2164031 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.and, [1, 4]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.or, [1, 8]⟩,
    ⟨.and, [2, 9]⟩,
    ⟨.or, [2, 9]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.not, [12]⟩,
    ⟨.or, [7, 13]⟩,
    ⟨.or, [10, 14]⟩
  ], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
