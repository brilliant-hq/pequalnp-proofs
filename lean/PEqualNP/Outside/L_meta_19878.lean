import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19878

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [13, 18]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [22, 18]⟩, ⟨.and, [0, 23]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [25, 14]⟩, ⟨.or, [26, 19]⟩, ⟨.and, [1, 27]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [2, 29]⟩, ⟨.or, [8, 17]⟩, ⟨.or, [31, 19]⟩, ⟨.and, [3, 32]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [4, 34]⟩, ⟨.or, [16, 21]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [40, 19]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [24, 28]⟩, ⟨.or, [43, 30]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [45, 35]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 39]⟩, ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 34 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (13073558080245330525 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19878

theorem PEqualNP.Outside.L_meta_19878 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13073558080245330525 : ℕ).testBit (8 * u.val + v.val)) 34) :=
  ⟨PEqualNP.Outside.L_meta_19878.witness, PEqualNP.Outside.L_meta_19878.mono, PEqualNP.Outside.L_meta_19878.small, PEqualNP.Outside.L_meta_19878.rep⟩
