import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22405 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (904047 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [6, 7]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [12, 15]⟩, ⟨.or, [14, 1]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [19, 18]⟩, ⟨.and, [17, 20]⟩, ⟨.or, [21, 16]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
