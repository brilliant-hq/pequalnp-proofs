import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19838 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9972273704342751540 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[
      ⟨.or, [10, 13]⟩,
      ⟨.or, [8, 11]⟩,
      ⟨.or, [9, 15]⟩,
      ⟨.or, [12, 16]⟩,
      ⟨.or, [15, 17]⟩,
      ⟨.or, [8, 12]⟩,
      ⟨.or, [14, 21]⟩,
      ⟨.or, [9, 10]⟩,
      ⟨.or, [14, 23]⟩,
      ⟨.or, [12, 17]⟩,
      ⟨.or, [13, 18]⟩,
      ⟨.or, [14, 16]⟩,
      ⟨.or, [11, 18]⟩,
      ⟨.and, [0, 19]⟩,
      ⟨.and, [1, 20]⟩,
      ⟨.and, [2, 22]⟩,
      ⟨.and, [3, 24]⟩,
      ⟨.and, [4, 25]⟩,
      ⟨.and, [5, 26]⟩,
      ⟨.and, [6, 27]⟩,
      ⟨.and, [7, 28]⟩,
      ⟨.or, [29, 30]⟩,
      ⟨.or, [31, 37]⟩,
      ⟨.or, [32, 38]⟩,
      ⟨.or, [33, 39]⟩,
      ⟨.or, [34, 40]⟩,
      ⟨.or, [35, 41]⟩,
      ⟨.or, [36, 42]⟩
    ], 43⟩
  refine ⟨witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.Monotone2, witness]
