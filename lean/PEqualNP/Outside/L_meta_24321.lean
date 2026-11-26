import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24321 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4377519 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 2]⟩, ⟨.not, [3]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [10, 11]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
