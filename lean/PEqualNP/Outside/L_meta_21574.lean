import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21574 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (17052119 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨(⟨[⟨.and, [0, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [5, 8]⟩, ⟨.not, [9]⟩], 10⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
