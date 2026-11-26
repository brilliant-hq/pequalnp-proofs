import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22692 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849709 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [5, 1]⟩, ⟨.and, [9, 0]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [15, 14]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [12, 4]⟩, ⟨.and, [18, 17]⟩, ⟨.or, [11, 19]⟩, ⟨.and, [13, 16]⟩, ⟨.and, [11, 17]⟩, ⟨.or, [21, 20]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
