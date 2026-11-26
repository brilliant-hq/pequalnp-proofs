import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24501 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147391 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [1, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [9, 10]⟩, ⟨.not, [11]⟩, ⟨.or, [8, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
