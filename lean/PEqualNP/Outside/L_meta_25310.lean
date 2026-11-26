import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25310 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165055 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.not, [8]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [6, 11]⟩, ⟨.and, [7, 12]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [0, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
