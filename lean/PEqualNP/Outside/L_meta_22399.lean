import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22399 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (903020 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 6]⟩, ⟨.and, [5, 3]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [12, 4]⟩, ⟨.and, [15, 13]⟩, ⟨.and, [14, 10]⟩, ⟨.or, [11, 9]⟩, ⟨.and, [18, 0]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [16, 7]⟩, ⟨.or, [20, 19]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
