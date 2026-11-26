import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20870 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31361057 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  refine ⟨⟨[⟨.or, [1, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [9, 14]⟩, ⟨.and, [11, 17]⟩, ⟨.or, [16, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
