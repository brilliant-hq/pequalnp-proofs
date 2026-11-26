import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22726 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883254 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [5, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [15, 13]⟩, ⟨.and, [5, 3]⟩, ⟨.and, [16, 11]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [19, 3]⟩, ⟨.and, [15, 12]⟩, ⟨.or, [21, 20]⟩, ⟨.or, [18, 22]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
