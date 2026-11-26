import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24431 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (53052 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.not, [8]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [6, 11]⟩, ⟨.and, [9, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
