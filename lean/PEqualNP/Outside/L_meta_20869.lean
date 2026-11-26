import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20869 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31354945 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  refine ⟨⟨[⟨.or, [0, 6]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [8, 12]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [14, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
