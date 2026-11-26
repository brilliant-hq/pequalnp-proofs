import PEqualNP.Defs

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_24127 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (267165 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨(⟨[
      ⟨.or, [3, 4]⟩,
      ⟨.or, [1, 4]⟩,
      ⟨.and, [2, 5]⟩,
      ⟨.or, [6, 7]⟩,
      ⟨.or, [2, 5]⟩,
      ⟨.or, [0, 1]⟩,
      ⟨.and, [9, 10]⟩,
      ⟨.not, [8]⟩,
      ⟨.or, [11, 12]⟩],
    13⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
