import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22353 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841134 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [4, 0]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [15, 14]⟩, ⟨.and, [12, 15]⟩, ⟨.and, [10, 16]⟩, ⟨.or, [8, 13]⟩, ⟨.and, [1, 19]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [18, 21]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
