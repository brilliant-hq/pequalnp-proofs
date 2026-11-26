import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20275 :
    PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 8 => (10543322878649664930 : ℕ).testBit (8 * u.val + v.val)) 25 := by
  refine ⟨(⟨[

    ⟨.or, [1, 13]⟩,
    ⟨.or, [2, 15]⟩,
    ⟨.or, [3, 14]⟩,
    ⟨.or, [4, 12]⟩,
    ⟨.or, [7, 11]⟩,

    ⟨.or, [0, 8]⟩,
    ⟨.or, [9, 16]⟩,
    ⟨.or, [22, 17]⟩,
    ⟨.or, [1, 8]⟩,
    ⟨.or, [24, 18]⟩,
    ⟨.or, [25, 19]⟩,
    ⟨.or, [6, 10]⟩,
    ⟨.or, [16, 20]⟩,
    ⟨.or, [5, 17]⟩,
    ⟨.or, [18, 20]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.or, [31, 19]⟩,

    ⟨.and, [21, 23]⟩,
    ⟨.and, [26, 27]⟩,
    ⟨.and, [28, 29]⟩,
    ⟨.and, [30, 32]⟩,
    ⟨.or, [33, 34]⟩,
    ⟨.or, [37, 35]⟩,
    ⟨.or, [38, 36]⟩], 39⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel
