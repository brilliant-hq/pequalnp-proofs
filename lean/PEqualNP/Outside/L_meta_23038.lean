import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23038 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (101948 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [3, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [2, 7]⟩,
      ⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [3, 10]⟩,
      ⟨.and, [9, 11]⟩, ⟨.or, [8, 12]⟩], 13⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.Monotone2]
