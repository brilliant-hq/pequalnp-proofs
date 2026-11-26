import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22999 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34074 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [0, 2]⟩,
    ⟨.and, [0, 4]⟩,
    ⟨.and, [3, 6]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.and, [1, 9]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [7, 11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
