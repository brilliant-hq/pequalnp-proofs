import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_20858 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (27396129 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨(⟨[⟨.or, [0, 1]⟩, ⟨.and, [10, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [14, 9]⟩, ⟨.and, [4, 15]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [17, 13]⟩, ⟨.or, [18, 16]⟩], 19⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
