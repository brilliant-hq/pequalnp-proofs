import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21351 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (128958 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  refine ⟨⟨[⟨.or, [6, 8]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [3, 12]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [10, 15]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [13, 17]⟩, ⟨.and, [16, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
