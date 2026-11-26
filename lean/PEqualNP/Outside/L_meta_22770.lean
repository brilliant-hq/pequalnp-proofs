import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22770 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947629 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[
    ⟨.or, [0, 5]⟩,
    ⟨.or, [6, 10]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.and, [14, 11]⟩,
    ⟨.and, [17, 20]⟩,
    ⟨.or, [21, 22]⟩
  ], 23⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
