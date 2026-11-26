import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24693 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16520 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.and, [0, 3]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [4, 8]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.not, [11]⟩,
    ⟨.or, [6, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
