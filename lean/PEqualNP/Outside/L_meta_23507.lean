import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23507 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (17175 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [1, 3]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [2, 4]⟩,
      ⟨.or, [5, 8]⟩, ⟨.or, [3, 9]⟩, ⟨.not, [10]⟩,
      ⟨.and, [7, 11]⟩, ⟨.or, [6, 12]⟩], 13⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.FanInTwo]
