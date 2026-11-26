import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22385 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843064 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [0, 6]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [13, 10]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [19, 14]⟩, ⟨.and, [16, 3]⟩, ⟨.or, [21, 20]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
