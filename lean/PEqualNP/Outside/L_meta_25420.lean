import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25420 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6508348 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [8, 12]⟩, ⟨.not, [10]⟩, ⟨.and, [13, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
