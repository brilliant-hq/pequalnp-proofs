import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24929 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4311355 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [3, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [6, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
