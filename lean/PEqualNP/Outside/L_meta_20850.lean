import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_20850 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (25957441 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨(⟨[⟨.and, [0, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [2, 12]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [17, 13]⟩, ⟨.or, [18, 16]⟩], 19⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
