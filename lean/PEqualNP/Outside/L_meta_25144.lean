import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25144 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630322109 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [6, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.not, [13]⟩], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide

