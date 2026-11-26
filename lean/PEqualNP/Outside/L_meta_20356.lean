import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20356 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (973835576939030640 : ℕ).testBit (8 * u.val + v.val)) 24) := by
  refine ⟨⟨[⟨.or, [7, 12]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [5, 18]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [16, 22]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [15, 19]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [20, 28]⟩, ⟨.or, [9, 15]⟩, ⟨.and, [29, 30]⟩, ⟨.and, [25, 24]⟩, ⟨.and, [31, 23]⟩, ⟨.and, [26, 27]⟩, ⟨.or, [32, 33]⟩, ⟨.or, [36, 34]⟩, ⟨.or, [37, 35]⟩], 38⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
