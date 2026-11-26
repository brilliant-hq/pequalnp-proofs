import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22323 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (840692 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [7, 6]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [11, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [16, 14]⟩, ⟨.and, [18, 13]⟩, ⟨.and, [17, 15]⟩, ⟨.or, [18, 8]⟩, ⟨.or, [20, 19]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
