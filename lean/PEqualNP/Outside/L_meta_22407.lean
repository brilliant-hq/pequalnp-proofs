import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22407 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (904061 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [7, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [11, 3]⟩, ⟨.or, [1, 0]⟩, ⟨.and, [12, 15]⟩, ⟨.or, [2, 0]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [17, 13]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [15, 4]⟩, ⟨.or, [21, 20]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
