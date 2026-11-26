import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24467 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (116665 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨(⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [6, 7]⟩, ⟨.not, [9]⟩, ⟨.and, [8, 10]⟩], 11⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
