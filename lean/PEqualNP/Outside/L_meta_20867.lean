import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_20867 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (30475297 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨(⟨[⟨.or, [0, 1]⟩, ⟨.or, [10, 2]⟩, ⟨.and, [11, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [14, 8]⟩, ⟨.or, [15, 9]⟩, ⟨.and, [4, 16]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [18, 17]⟩], 19⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
