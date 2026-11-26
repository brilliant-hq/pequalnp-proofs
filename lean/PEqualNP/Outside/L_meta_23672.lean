import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23672 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (36156 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 0]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [1, 0]⟩,
             ⟨.or, [4, 2]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [8, 10]⟩,
             ⟨.or, [7, 11]⟩], 12⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp
  · decide
