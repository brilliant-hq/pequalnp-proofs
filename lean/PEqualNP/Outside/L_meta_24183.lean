import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24183 :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
        ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
          (283484 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [1, 3]⟩,
            ⟨.and, [2, 5]⟩,
            ⟨.or, [0, 4]⟩,
            ⟨.or, [0, 1]⟩,
            ⟨.or, [3, 4]⟩,
            ⟨.and, [8, 9]⟩,
            ⟨.or, [2, 10]⟩,
            ⟨.not, [11]⟩,
            ⟨.and, [7, 12]⟩,
            ⟨.or, [6, 13]⟩,
            ⟨.not, [14]⟩], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
  · decide +kernel
