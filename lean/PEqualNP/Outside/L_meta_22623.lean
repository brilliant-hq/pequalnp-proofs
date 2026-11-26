import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22623 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (17180 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [0, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩,
      ⟨.or, [3, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [1, 10]⟩,
      ⟨.or, [0, 11]⟩, ⟨.and, [7, 12]⟩, ⟨.or, [6, 13]⟩], 14⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.FanInTwo]
