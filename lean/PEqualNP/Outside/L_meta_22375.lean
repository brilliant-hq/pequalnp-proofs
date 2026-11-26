import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22375 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841662 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [4, 0]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [8, 14]⟩, ⟨.and, [16, 17]⟩, ⟨.and, [10, 9]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [20, 21]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
