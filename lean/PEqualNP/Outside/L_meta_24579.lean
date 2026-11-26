import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24579 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6410044 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.not, [5]⟩,
    ⟨.and, [6, 8]⟩,
    ⟨.and, [7, 9]⟩,
    ⟨.or, [10, 11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
