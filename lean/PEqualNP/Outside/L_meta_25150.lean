import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25150 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630388407 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [2, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.not, [13]⟩], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide

