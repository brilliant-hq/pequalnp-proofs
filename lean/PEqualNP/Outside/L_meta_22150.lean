import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22150 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16794 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.not, [0]⟩,
    ⟨.and, [3, 6]⟩,
    ⟨.not, [0]⟩,
    ⟨.and, [4, 8]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [10, 4]⟩,
    ⟨.not, [11]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.or, [14, 9]⟩,
    ⟨.or, [15, 13]⟩,
    ⟨.not, [16]⟩
  ], 17⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
