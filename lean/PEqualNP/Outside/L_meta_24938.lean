import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24938 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4312892 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [3, 5]⟩, ⟨.not, [5]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [4, 7]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
