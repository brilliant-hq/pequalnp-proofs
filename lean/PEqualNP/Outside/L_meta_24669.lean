import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24669 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630321599 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨(⟨[⟨.or, [1, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.not, [12]⟩], 13⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
