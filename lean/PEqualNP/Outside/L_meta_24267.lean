import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24267 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16798 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.not, [8]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [9, 11]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
