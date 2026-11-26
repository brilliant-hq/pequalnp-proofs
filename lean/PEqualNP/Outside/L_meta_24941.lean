import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24941 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4344239 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 4]⟩, ⟨.not, [3]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [9, 10]⟩, ⟨.not, [4]⟩, ⟨.or, [3, 12]⟩, ⟨.and, [11, 13]⟩], 14⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
