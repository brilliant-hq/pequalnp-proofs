import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25281 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147771 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [2]⟩, ⟨.and, [1, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [9, 11]⟩, ⟨.not, [12]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [8, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
