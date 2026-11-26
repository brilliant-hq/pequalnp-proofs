import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22689 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843196 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [1, 7]⟩, ⟨.and, [4, 2]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [13, 1]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [13, 2]⟩, ⟨.and, [18, 16]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [17, 3]⟩, ⟨.and, [21, 20]⟩, ⟨.or, [22, 19]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
