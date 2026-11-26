import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21883 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 4 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (1855 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [2, 3]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 8]⟩], 9⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.Monotone2]
