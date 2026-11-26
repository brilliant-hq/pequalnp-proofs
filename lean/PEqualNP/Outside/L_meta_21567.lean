import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21567 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (274896 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.not, [0]⟩, ⟨.not, [4]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [4, 8]⟩, ⟨.and, [7, 9]⟩], 10⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
