import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24895 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2215869 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.and, [2, 4]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.not, [7]⟩,
    ⟨.or, [0, 8]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.not, [11]⟩,
    ⟨.and, [12, 13]⟩
  ], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
