import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24961 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6374815 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [2, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [1, 3]⟩, ⟨.not, [10]⟩, ⟨.and, [11, 13]⟩], 14⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
