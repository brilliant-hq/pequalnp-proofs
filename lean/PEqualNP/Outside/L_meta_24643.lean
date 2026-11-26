import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24643 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274876863 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.not, [5]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.not, [10]⟩, ⟨.and, [11, 12]⟩], 13⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
