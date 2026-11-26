import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22292 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (837617 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [9, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [5, 11]⟩, ⟨.and, [8, 1]⟩, ⟨.or, [13, 12]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [3, 1]⟩, ⟨.and, [17, 18]⟩, ⟨.and, [14, 19]⟩, ⟨.or, [20, 21]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
