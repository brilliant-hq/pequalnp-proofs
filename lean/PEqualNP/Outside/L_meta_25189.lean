import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25189 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17981 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.not, [7]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [7, 11]⟩, ⟨.not, [12]⟩, ⟨.or, [13, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
