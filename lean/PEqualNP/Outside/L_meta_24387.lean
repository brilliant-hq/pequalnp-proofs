import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24387 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630388415 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.not, [11]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
