import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19932

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 11]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [0, 20]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [24, 19]⟩, ⟨.and, [2, 25]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [27, 16]⟩, ⟨.and, [3, 28]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [30, 16]⟩, ⟨.and, [4, 31]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [33, 12]⟩, ⟨.or, [34, 15]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [6, 37]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [39, 17]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [21, 23]⟩, ⟨.or, [42, 26]⟩, ⟨.or, [43, 29]⟩, ⟨.or, [44, 32]⟩, ⟨.or, [45, 36]⟩, ⟨.or, [46, 38]⟩, ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 33 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (16436895475263517410 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19932

theorem PEqualNP.Outside.L_meta_19932 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16436895475263517410 : ℕ).testBit (8 * u.val + v.val)) 33) :=
  ⟨PEqualNP.Outside.L_meta_19932.witness, PEqualNP.Outside.L_meta_19932.mono, PEqualNP.Outside.L_meta_19932.small, PEqualNP.Outside.L_meta_19932.rep⟩
