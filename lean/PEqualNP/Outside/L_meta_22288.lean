import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22288 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (837101 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [6, 7]⟩, ⟨.or, [3, 1]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [11, 10]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [5, 13]⟩, ⟨.and, [14, 17]⟩, ⟨.and, [0, 15]⟩, ⟨.and, [1, 16]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [21, 19]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
