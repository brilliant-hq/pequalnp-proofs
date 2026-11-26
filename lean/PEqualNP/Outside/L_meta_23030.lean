import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23030 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (36156 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 2]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [0, 1]⟩,
      ⟨.or, [4, 5]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [8, 10]⟩,
      ⟨.or, [7, 11]⟩], 12⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.Monotone2]
