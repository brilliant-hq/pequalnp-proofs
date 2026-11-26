import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24660 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (551767999 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨(⟨[⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [4, 5]⟩, ⟨.not, [6]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [10, 12]⟩], 13⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
