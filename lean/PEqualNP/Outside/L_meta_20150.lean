import PEqualNP.Defs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20150 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5515944280522376865 : ℕ).testBit (8 * u.val + v.val)) 27) := by
  refine ⟨⟨[
      ⟨.or, [0, 10]⟩,
      ⟨.or, [1, 8]⟩,
      ⟨.or, [2, 12]⟩,
      ⟨.or, [3, 14]⟩,
      ⟨.or, [4, 9]⟩,
      ⟨.or, [5, 11]⟩,
      ⟨.or, [6, 15]⟩,
      ⟨.or, [7, 13]⟩,
      ⟨.or, [17, 18]⟩,
      ⟨.or, [24, 21]⟩,
      ⟨.and, [20, 25]⟩,
      ⟨.or, [16, 19]⟩,
      ⟨.or, [17, 23]⟩,
      ⟨.and, [27, 28]⟩,
      ⟨.or, [19, 13]⟩,
      ⟨.and, [18, 30]⟩,
      ⟨.or, [16, 21]⟩,
      ⟨.or, [22, 7]⟩,
      ⟨.and, [32, 33]⟩,
      ⟨.or, [21, 15]⟩,
      ⟨.or, [6, 12]⟩,
      ⟨.and, [35, 36]⟩,
      ⟨.or, [26, 29]⟩,
      ⟨.or, [38, 31]⟩,
      ⟨.or, [39, 34]⟩,
      ⟨.or, [40, 37]⟩
    ], 41⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide
