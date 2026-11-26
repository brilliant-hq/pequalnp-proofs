import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24775 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (118333 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.not, [7]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [11, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
