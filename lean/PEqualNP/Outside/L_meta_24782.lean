import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24782 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧
        ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (2113727 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [2, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 3]⟩,
    ⟨.or, [7, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [1, 2]⟩,
    ⟨.or, [10, 11]⟩, ⟨.not, [12]⟩, ⟨.or, [0, 13]⟩], 14⟩,
    ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
