import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24785 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2113977 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.not, [6]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [0, 3]⟩, ⟨.not, [9]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [11, 12]⟩, ⟨.not, [13]⟩], 14⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
