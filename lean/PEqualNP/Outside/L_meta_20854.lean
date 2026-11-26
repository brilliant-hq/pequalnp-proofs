import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_20854 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (27004993 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨(⟨[⟨.and, [6, 1]⟩, ⟨.and, [7, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [17, 13]⟩, ⟨.or, [18, 16]⟩], 19⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
