import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22585 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (441 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [4, 5]⟩,
      ⟨.or, [3, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [7, 10]⟩,
      ⟨.not, [11]⟩, ⟨.and, [6, 12]⟩], 13⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.FanInTwo]
