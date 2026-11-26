import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25042 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270583715 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.not, [5]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [9, 10]⟩, ⟨.not, [12]⟩, ⟨.and, [11, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
