import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24583 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6540991 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [1, 3]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.and, [3, 5]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.not, [11]⟩,
    ⟨.and, [8, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
