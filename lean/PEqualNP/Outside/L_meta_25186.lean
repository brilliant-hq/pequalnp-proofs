import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25186 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17967 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.not, [12]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [8, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
