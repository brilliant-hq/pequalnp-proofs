import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22381 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843004 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [8, 2]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [13, 12]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [5, 13]⟩, ⟨.and, [14, 16]⟩, ⟨.and, [15, 18]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [20, 19]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
