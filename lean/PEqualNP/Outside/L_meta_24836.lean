import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24836 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2164639 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [2, 4]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.not, [11]⟩, ⟨.and, [12, 13]⟩], 14⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
