import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24186 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266774 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨(⟨[⟨.or, [1, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 4]⟩, ⟨.not, [0]⟩, ⟨.or, [2, 5]⟩, ⟨.not, [9]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [3, 5]⟩, ⟨.not, [12]⟩, ⟨.and, [2, 13]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [15, 11]⟩, ⟨.or, [16, 14]⟩], 17⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
