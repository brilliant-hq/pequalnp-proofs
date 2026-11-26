import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22417 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1865342 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [5, 1]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [14, 13]⟩, ⟨.and, [13, 2]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [19, 0]⟩, ⟨.and, [20, 21]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
