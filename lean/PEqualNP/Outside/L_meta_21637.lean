import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21637 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8606 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [1, 2]⟩,
      ⟨.or, [0, 3]⟩,
      ⟨.or, [3, 4]⟩,
      ⟨.and, [0, 7]⟩,
      ⟨.or, [2, 8]⟩,
      ⟨.or, [1, 9]⟩,
      ⟨.and, [6, 10]⟩,
      ⟨.or, [5, 11]⟩], 12⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro gate h
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Set.mem_insert_iff, Set.mem_singleton_iff]
