import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24877 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2199227 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.not, [2]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [5, 10]⟩, ⟨.not, [11]⟩, ⟨.or, [6, 12]⟩, ⟨.and, [9, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
