import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20873 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31654945 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  refine ⟨⟨[⟨.or, [8, 9]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [0, 13]⟩, ⟨.and, [5, 15]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [14, 17]⟩, ⟨.or, [16, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
