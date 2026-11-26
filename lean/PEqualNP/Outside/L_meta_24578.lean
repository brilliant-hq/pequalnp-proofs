import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24578 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6408126 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [1, 3]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.not, [5]⟩,
    ⟨.and, [9, 10]⟩,
    ⟨.or, [8, 11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
