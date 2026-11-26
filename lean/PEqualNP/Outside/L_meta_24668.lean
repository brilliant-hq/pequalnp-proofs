import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24668 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630321343 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [9, 11]⟩, ⟨.not, [12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
