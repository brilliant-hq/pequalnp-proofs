import PEqualNP.Defs

set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.L_meta_22232 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851255 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  -- Cover columns 0–1 in rows 0, 2, 3; columns 2, 4, 5 in rows 0–1;
  -- and columns 2–3 in row 2.
  refine ⟨⟨[
    ⟨.or, [4, 5]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [12, 3]⟩,
    ⟨.and, [10, 13]⟩,
    ⟨.or, [6, 11]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.and, [15, 16]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.and, [18, 2]⟩,
    ⟨.or, [14, 17]⟩,
    ⟨.or, [20, 19]⟩
  ], 21⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
