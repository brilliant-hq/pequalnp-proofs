import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24392 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34634582183 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [8, 10]⟩, ⟨.not, [11]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
