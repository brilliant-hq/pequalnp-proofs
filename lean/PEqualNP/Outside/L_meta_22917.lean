import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22917 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧
      ∀ i j : Fin 5,
        C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
          (9116 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩,
      ⟨.or, [2, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [5, 9]⟩], 10⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.Monotone2]
