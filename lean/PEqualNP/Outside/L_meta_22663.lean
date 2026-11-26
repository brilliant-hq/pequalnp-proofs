import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22663 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841212 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [6, 8]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [13, 2]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [6, 17]⟩, ⟨.or, [16, 15]⟩, ⟨.and, [19, 20]⟩, ⟨.and, [16, 18]⟩, ⟨.or, [21, 22]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
