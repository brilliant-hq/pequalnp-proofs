import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21717 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283481 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [9, 2]⟩, ⟨.not, [10]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [13, 12]⟩, ⟨.not, [14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
