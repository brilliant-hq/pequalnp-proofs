import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23029 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36152 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [0, 3]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
