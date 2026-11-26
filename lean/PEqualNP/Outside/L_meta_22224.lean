import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22224 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849711 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨(⟨[⟨.and, [8, 1]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [2, 0]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [15, 16]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [20, 17]⟩], 21⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
