import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24841 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165439 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [2, 4]⟩, ⟨.not, [8]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
