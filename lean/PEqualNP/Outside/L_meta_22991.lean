import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22991 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (830 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [1, 7]⟩,
      ⟨.and, [0, 8]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [2, 10]⟩,
      ⟨.and, [6, 11]⟩], 12⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.Monotone2]
