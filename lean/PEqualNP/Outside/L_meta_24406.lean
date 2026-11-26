import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24406 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50072 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [0, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [6, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
