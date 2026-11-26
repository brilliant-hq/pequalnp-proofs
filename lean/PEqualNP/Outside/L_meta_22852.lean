import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22852 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (908158 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨⟨[⟨.or, [6, 7]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [12, 11]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [14, 9]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 13]⟩, ⟨.and, [1, 15]⟩, ⟨.and, [2, 16]⟩, ⟨.and, [3, 17]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [22, 20]⟩, ⟨.or, [23, 21]⟩], 24⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
