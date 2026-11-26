import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22284 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (836982 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [8, 6]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [5, 2]⟩, ⟨.or, [5, 1]⟩, ⟨.or, [14, 9]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [12, 15]⟩, ⟨.and, [14, 12]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [19, 18]⟩, ⟨.and, [11, 2]⟩, ⟨.or, [20, 21]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
