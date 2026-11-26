import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24700 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16571 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨(⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [7, 9]⟩, ⟨.not, [11]⟩, ⟨.or, [10, 12]⟩], 13⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
