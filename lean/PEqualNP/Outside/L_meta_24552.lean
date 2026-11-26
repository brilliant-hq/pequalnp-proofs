import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24552 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4295599 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.and, [2, 3]⟩, ⟨.not, [4]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [9, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
