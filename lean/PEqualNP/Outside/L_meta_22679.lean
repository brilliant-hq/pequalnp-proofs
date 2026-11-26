import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22679 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843063 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [0, 3]⟩, ⟨.or, [4, 2]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [1, 0]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [12, 2]⟩, ⟨.or, [6, 13]⟩, ⟨.and, [14, 18]⟩, ⟨.or, [19, 17]⟩, ⟨.and, [16, 15]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [20, 21]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
