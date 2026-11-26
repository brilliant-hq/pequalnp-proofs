import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23880 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧
      ∀ i j : Fin 5,
        C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
          (8925 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩,
      ⟨.and, [1, 7]⟩, ⟨.not, [8]⟩, ⟨.and, [6, 9]⟩,
      ⟨.or, [5, 10]⟩], 11⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.FanInTwo]
