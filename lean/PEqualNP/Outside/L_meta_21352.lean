import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21352 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (237370 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  refine ⟨⟨[⟨.or, [1, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [13, 15]⟩, ⟨.and, [14, 17]⟩, ⟨.and, [16, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
