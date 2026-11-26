import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22422 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881340 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[
    ⟨.or, [3, 7]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [1, 8]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.and, [14, 10]⟩,
    ⟨.and, [12, 17]⟩,
    ⟨.and, [1, 8]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.or, [21, 20]⟩
  ], 22⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
