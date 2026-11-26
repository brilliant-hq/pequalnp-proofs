import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22705 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (904053 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [4, 6]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [2, 1]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [1, 0]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [5, 0]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [17, 16]⟩, ⟨.and, [12, 11]⟩, ⟨.or, [15, 20]⟩, ⟨.and, [18, 19]⟩, ⟨.or, [21, 22]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
