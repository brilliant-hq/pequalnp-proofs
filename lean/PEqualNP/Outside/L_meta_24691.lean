import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24691 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (409 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [0, 8]⟩,
    ⟨.and, [7, 9]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.not, [11]⟩,
    ⟨.and, [6, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
