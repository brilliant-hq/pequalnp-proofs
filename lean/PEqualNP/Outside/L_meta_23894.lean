import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23894 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266335 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨(⟨[⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [0, 10]⟩], 11⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
