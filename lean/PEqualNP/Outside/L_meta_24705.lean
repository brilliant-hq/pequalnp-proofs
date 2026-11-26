import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24705 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16912 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.and, [0, 4]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.or, [6, 10]⟩,
    ⟨.not, [11]⟩,
    ⟨.or, [8, 12]⟩,
    ⟨.or, [7, 13]⟩
  ], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
