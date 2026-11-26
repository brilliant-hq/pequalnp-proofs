import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24091 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (549853 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 1]⟩, ⟨.not, [6]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [2, 9]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [8, 12]⟩], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
