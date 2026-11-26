import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20209 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6616700159142438735 : ℕ).testBit (8 * u.val + v.val)) 30) := by
  refine ⟨⟨[⟨.or, [7, 13]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [5, 18]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [12, 19]⟩, ⟨.or, [6, 17]⟩, ⟨.or, [15, 21]⟩, ⟨.or, [3, 24]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [17, 28]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [20, 25]⟩, ⟨.or, [6, 23]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [18, 22]⟩, ⟨.or, [20, 33]⟩, ⟨.or, [19, 30]⟩, ⟨.or, [16, 26]⟩, ⟨.or, [8, 29]⟩, ⟨.and, [35, 32]⟩, ⟨.and, [34, 31]⟩, ⟨.and, [38, 36]⟩, ⟨.and, [27, 37]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [43, 41]⟩, ⟨.or, [44, 42]⟩], 45⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
