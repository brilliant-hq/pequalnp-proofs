import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22363 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841522 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [0, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [5, 1]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [15, 11]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [12, 16]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [4, 17]⟩, ⟨.or, [20, 19]⟩, ⟨.or, [18, 21]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
