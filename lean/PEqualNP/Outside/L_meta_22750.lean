import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22750 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1939434 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [6, 5]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [3, 1]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [15, 0]⟩, ⟨.or, [4, 14]⟩, ⟨.and, [10, 13]⟩, ⟨.and, [12, 17]⟩, ⟨.and, [4, 13]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [22, 21]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
