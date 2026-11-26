import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23225 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (36148 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩,
      ⟨.or, [2, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [6, 10]⟩], 11⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.FanInTwo]
