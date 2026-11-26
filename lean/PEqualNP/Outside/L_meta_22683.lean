import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22683 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843126 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [9, 8]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [5, 1]⟩, ⟨.and, [14, 15]⟩, ⟨.and, [13, 2]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [11, 18]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [14, 15]⟩, ⟨.and, [21, 19]⟩, ⟨.or, [17, 22]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
