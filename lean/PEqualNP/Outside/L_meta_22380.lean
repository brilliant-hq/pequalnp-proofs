import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22380 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (842996 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [5, 4]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [11, 10]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [14, 9]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [4, 0]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [15, 6]⟩, ⟨.and, [19, 17]⟩, ⟨.or, [20, 12]⟩, ⟨.or, [21, 18]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
