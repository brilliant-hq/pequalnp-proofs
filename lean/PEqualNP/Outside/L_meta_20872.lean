import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20872 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31523873 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [4, 13]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [14, 17]⟩, ⟨.and, [11, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
