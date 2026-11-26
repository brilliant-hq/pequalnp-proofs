import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19711

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 9]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [10, 20]⟩, ⟨.and, [0, 21]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [23, 17]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [2, 26]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [28, 18]⟩, ⟨.and, [3, 29]⟩, ⟨.or, [16, 17]⟩, ⟨.and, [4, 31]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [33, 18]⟩, ⟨.and, [5, 34]⟩, ⟨.or, [15, 20]⟩, ⟨.and, [6, 36]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [38, 19]⟩, ⟨.and, [7, 39]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [41, 27]⟩, ⟨.or, [42, 30]⟩, ⟨.or, [43, 32]⟩, ⟨.or, [44, 35]⟩, ⟨.or, [45, 37]⟩, ⟨.or, [46, 40]⟩], 47⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 32 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (17339788871490640935 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19711

theorem PEqualNP.Outside.L_meta_19711 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17339788871490640935 : ℕ).testBit (8 * u.val + v.val)) 32) :=
  ⟨PEqualNP.Outside.L_meta_19711.witness, PEqualNP.Outside.L_meta_19711.mono, PEqualNP.Outside.L_meta_19711.small, PEqualNP.Outside.L_meta_19711.rep⟩
