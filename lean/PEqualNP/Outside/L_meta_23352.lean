import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23352 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (50972 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [4, 5]⟩, ⟨.not, [6]⟩, ⟨.and, [2, 7]⟩,
      ⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [9, 10]⟩,
      ⟨.or, [8, 11]⟩], 12⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.FanInTwo]
