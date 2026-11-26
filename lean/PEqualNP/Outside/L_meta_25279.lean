import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25279 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147763 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [3, 4]⟩,
    ⟨.and, [1, 6]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.not, [8]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [3, 2]⟩,
    ⟨.and, [10, 9]⟩,
    ⟨.and, [8, 11]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.not, [14]⟩
  ], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
