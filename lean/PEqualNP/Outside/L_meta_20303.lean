import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20303 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15611213044641773910 : ℕ).testBit (8 * u.val + v.val)) 26) := by
  refine ⟨⟨[⟨.or, [1, 10]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [4, 18]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [20, 21]⟩, ⟨.or, [12, 22]⟩, ⟨.or, [15, 19]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [3, 17]⟩, ⟨.or, [24, 26]⟩, ⟨.or, [2, 13]⟩, ⟨.or, [4, 19]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [21, 28]⟩, ⟨.or, [13, 29]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [2, 20]⟩, ⟨.and, [30, 23]⟩, ⟨.and, [25, 32]⟩, ⟨.and, [33, 34]⟩, ⟨.and, [27, 31]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [39, 37]⟩, ⟨.or, [40, 38]⟩], 41⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
