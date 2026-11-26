import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22294 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (838774 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [5, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [12, 3]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [5, 13]⟩, ⟨.and, [17, 0]⟩, ⟨.and, [16, 1]⟩, ⟨.and, [15, 14]⟩, ⟨.or, [20, 19]⟩, ⟨.or, [18, 21]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
