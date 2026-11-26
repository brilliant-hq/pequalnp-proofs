import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22368 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841534 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [3, 6]⟩, ⟨.or, [4, 0]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [14, 5]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [17, 18]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [19, 21]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
