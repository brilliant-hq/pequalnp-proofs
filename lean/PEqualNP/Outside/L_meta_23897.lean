import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23897 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266704 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [0, 4]⟩,
      ⟨.or, [0, 4]⟩,
      ⟨.and, [2, 3]⟩,
      ⟨.or, [7, 6]⟩,
      ⟨.not, [8]⟩,
      ⟨.or, [5, 9]⟩], 10⟩
  refine ⟨witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, witness]
  · decide +kernel
