import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23645 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34612 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [0, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [6, 8]⟩,
      ⟨.or, [0, 1]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [9, 12]⟩], 13⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · intro gate hgate
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hgate
    rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
