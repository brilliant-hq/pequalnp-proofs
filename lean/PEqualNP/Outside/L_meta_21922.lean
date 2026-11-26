import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21922 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33550 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [1, 9]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [11, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
