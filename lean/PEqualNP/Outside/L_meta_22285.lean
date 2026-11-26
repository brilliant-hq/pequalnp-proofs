import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22285 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (836983 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [3, 6]⟩, ⟨.and, [9, 0]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [5, 2]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [14, 4]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [0, 16]⟩, ⟨.and, [15, 17]⟩, ⟨.and, [19, 18]⟩, ⟨.or, [21, 20]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
