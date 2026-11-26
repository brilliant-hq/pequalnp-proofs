import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22364 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841523 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [6, 0]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [10, 9]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [1, 17]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [18, 19]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [20, 21]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
