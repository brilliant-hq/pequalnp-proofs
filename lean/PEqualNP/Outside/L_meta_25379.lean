import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25379 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6374839 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.or, [5, 8]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [3, 10]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [7, 13]⟩,
    ⟨.not, [14]⟩
  ], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
