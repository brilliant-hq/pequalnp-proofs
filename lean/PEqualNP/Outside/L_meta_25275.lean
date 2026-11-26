import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25275 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147645 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [0]⟩, ⟨.not, [2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [9, 10]⟩, ⟨.not, [12]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [13, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
