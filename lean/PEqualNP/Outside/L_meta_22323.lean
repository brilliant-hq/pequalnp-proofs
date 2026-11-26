import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22323 :
    PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 6) => (840692 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [6, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [0, 11]⟩,
      ⟨.or, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [13, 14]⟩,
      ⟨.or, [1, 2]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [7, 17]⟩,
      ⟨.and, [16, 18]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [19, 20]⟩], 21⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.Monotone2]
