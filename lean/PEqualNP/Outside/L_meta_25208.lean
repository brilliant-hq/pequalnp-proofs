import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25208 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33964 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.not, [13]⟩, ⟨.and, [12, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
