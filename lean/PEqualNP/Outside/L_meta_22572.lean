import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22572 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (34086 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [0, 4]⟩,
      ⟨.or, [1, 5]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [2, 10]⟩,
      ⟨.and, [7, 11]⟩], 12⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.FanInTwo]
