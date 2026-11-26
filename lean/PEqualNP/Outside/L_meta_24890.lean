import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24890 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2215359 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [2, 3]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.and, [3, 7]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.and, [6, 10]⟩,
    ⟨.not, [11]⟩,
    ⟨.and, [8, 12]⟩,
    ⟨.or, [0, 13]⟩
  ], 14⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
