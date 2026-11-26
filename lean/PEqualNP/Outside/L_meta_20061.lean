import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_20061 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17604493529221135470 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  let C : Circuit :=
    { gates := [
        ⟨.or, [1, 7]⟩,
        ⟨.or, [11, 14]⟩,
        ⟨.or, [0, 6]⟩,
        ⟨.or, [1, 5]⟩,
        ⟨.or, [9, 10]⟩,
        ⟨.or, [8, 9]⟩,
        ⟨.or, [5, 7]⟩,
        ⟨.or, [17, 20]⟩,
        ⟨.or, [10, 12]⟩,
        ⟨.or, [0, 16]⟩,
        ⟨.or, [2, 3]⟩,
        ⟨.or, [4, 26]⟩,
        ⟨.or, [4, 16]⟩,
        ⟨.or, [15, 21]⟩,
        ⟨.or, [3, 19]⟩,
        ⟨.or, [2, 25]⟩,
        ⟨.or, [11, 12]⟩,
        ⟨.or, [13, 14]⟩,
        ⟨.or, [13, 15]⟩,
        ⟨.or, [5, 6]⟩,
        ⟨.and, [18, 23]⟩,
        ⟨.and, [27, 29]⟩,
        ⟨.and, [30, 32]⟩,
        ⟨.and, [31, 33]⟩,
        ⟨.and, [24, 28]⟩,
        ⟨.and, [22, 34]⟩,
        ⟨.and, [8, 35]⟩,
        ⟨.or, [36, 37]⟩,
        ⟨.or, [38, 43]⟩,
        ⟨.or, [39, 44]⟩,
        ⟨.or, [40, 45]⟩,
        ⟨.or, [41, 46]⟩,
        ⟨.or, [42, 47]⟩]
      output := 48 }
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
