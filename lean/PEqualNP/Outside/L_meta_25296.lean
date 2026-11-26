import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25296 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2150206 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.not, [10]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
