import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24977 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6410173 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.not, [6]⟩, ⟨.not, [8]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [7, 12]⟩, ⟨.not, [13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
