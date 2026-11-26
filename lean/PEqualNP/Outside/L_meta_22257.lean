import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22257 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (817016 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [4, 0]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [2, 15]⟩, ⟨.and, [13, 11]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [16, 7]⟩, ⟨.and, [18, 19]⟩, ⟨.or, [8, 17]⟩, ⟨.or, [20, 17]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
