import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24709 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16948 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨(⟨[⟨.and, [1, 3]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [7, 8]⟩, ⟨.not, [10]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [6, 13]⟩], 14⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
