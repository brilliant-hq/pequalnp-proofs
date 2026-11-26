import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24639 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274845503 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.not, [5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [3, 7]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [11, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
