import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22423 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17074 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [1, 2]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [0, 8]⟩, ⟨.not, [3]⟩, ⟨.not, [6]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [9, 12]⟩, ⟨.not, [13]⟩, ⟨.and, [11, 14]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [7, 15]⟩, ⟨.and, [12, 17]⟩, ⟨.or, [16, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
