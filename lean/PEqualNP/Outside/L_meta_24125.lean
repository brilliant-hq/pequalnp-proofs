import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24125 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266905 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [1, 8]⟩, ⟨.not, [10]⟩, ⟨.or, [6, 11]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [12, 13]⟩], 14⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
