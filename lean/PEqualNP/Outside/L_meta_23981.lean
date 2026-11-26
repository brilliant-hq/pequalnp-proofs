import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23981 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12763 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨(⟨[⟨.and, [0, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.not, [4]⟩, ⟨.not, [5]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [8, 10]⟩], 11⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
