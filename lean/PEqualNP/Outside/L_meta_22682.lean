import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22682 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843070 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [9, 6]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [6, 13]⟩, ⟨.and, [11, 1]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [16, 15]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [18, 11]⟩, ⟨.and, [19, 21]⟩, ⟨.or, [22, 17]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
