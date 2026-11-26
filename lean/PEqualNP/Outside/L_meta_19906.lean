import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19906

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 10]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [14, 18]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [1, 21]⟩, ⟨.or, [15, 18]⟩, ⟨.and, [2, 23]⟩, ⟨.or, [13, 17]⟩, ⟨.and, [3, 25]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [27, 12]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [30, 14]⟩, ⟨.and, [5, 31]⟩, ⟨.or, [11, 17]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [11, 16]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [37, 24]⟩, ⟨.or, [38, 26]⟩, ⟨.or, [39, 29]⟩, ⟨.or, [40, 32]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 36]⟩], 43⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 28 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (975669345196721520 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19906

theorem PEqualNP.Outside.L_meta_19906 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (975669345196721520 : ℕ).testBit (8 * u.val + v.val)) 28) :=
  ⟨PEqualNP.Outside.L_meta_19906.witness, PEqualNP.Outside.L_meta_19906.mono, PEqualNP.Outside.L_meta_19906.small, PEqualNP.Outside.L_meta_19906.rep⟩
