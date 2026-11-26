import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22847 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (12783551 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 7]⟩,
      ⟨.or, [1, 8]⟩, ⟨.or, [0, 9]⟩], 10⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.FanInTwo]
