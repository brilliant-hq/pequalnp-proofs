import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24920 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4296508 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [3, 2]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [4, 10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [7, 13]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
