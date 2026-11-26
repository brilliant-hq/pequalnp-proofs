import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22994 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33558 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [0, 3]⟩,
    ⟨.and, [0, 4]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.and, [6, 9]⟩,
    ⟨.or, [1, 10]⟩,
    ⟨.and, [8, 11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
