import PEqualNP.Defs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20173 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15178139455177243725 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  refine ⟨{ gates := [
      ⟨.or, [4, 8]⟩,
      ⟨.or, [1, 15]⟩,
      ⟨.or, [9, 0]⟩,
      ⟨.or, [2, 17]⟩,
      ⟨.or, [10, 7]⟩,
      ⟨.or, [3, 13]⟩,
      ⟨.or, [19, 18]⟩,
      ⟨.or, [21, 18]⟩,
      ⟨.or, [5, 20]⟩,
      ⟨.or, [2, 16]⟩,
      ⟨.or, [16, 22]⟩,
      ⟨.or, [18, 5]⟩,
      ⟨.or, [14, 27]⟩,
      ⟨.or, [14, 6]⟩,
      ⟨.or, [6, 11]⟩,
      ⟨.or, [21, 24]⟩,
      ⟨.or, [20, 16]⟩,
      ⟨.or, [29, 25]⟩,
      ⟨.or, [12, 19]⟩,
      ⟨.and, [23, 33]⟩,
      ⟨.and, [28, 32]⟩,
      ⟨.and, [26, 30]⟩,
      ⟨.or, [35, 37]⟩,
      ⟨.and, [31, 34]⟩,
      ⟨.or, [38, 39]⟩,
      ⟨.or, [40, 36]⟩,
      ⟨.and, [1, 12]⟩,
      ⟨.or, [41, 42]⟩],
            output := 43 }, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide
