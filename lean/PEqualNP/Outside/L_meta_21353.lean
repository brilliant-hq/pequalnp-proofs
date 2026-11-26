import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21353 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (237374 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  refine ⟨⟨[⟨.or, [2, 7]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [11, 14]⟩, ⟨.or, [11, 14]⟩, ⟨.and, [13, 16]⟩, ⟨.and, [11, 15]⟩, ⟨.or, [17, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
