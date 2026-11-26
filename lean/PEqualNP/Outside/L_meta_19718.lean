import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19718

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 9]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [8, 22]⟩, ⟨.and, [0, 23]⟩, ⟨.or, [15, 22]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [2, 27]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [3, 29]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [31, 19]⟩, ⟨.and, [4, 32]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [5, 34]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [36, 18]⟩, ⟨.and, [6, 37]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [39, 21]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [24, 26]⟩, ⟨.or, [42, 28]⟩, ⟨.or, [43, 30]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [45, 35]⟩, ⟨.or, [46, 38]⟩, ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 33 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (7482418488621907005 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19718

theorem PEqualNP.Outside.L_meta_19718 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7482418488621907005 : ℕ).testBit (8 * u.val + v.val)) 33) :=
  ⟨PEqualNP.Outside.L_meta_19718.witness, PEqualNP.Outside.L_meta_19718.mono, PEqualNP.Outside.L_meta_19718.small, PEqualNP.Outside.L_meta_19718.rep⟩
