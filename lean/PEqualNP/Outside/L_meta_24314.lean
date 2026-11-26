import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24314 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4310950 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨(⟨[⟨.and, [0, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.not, [5]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [10, 11]⟩], 12⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
