import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19770

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 15]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [11, 20]⟩, ⟨.and, [0, 21]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [23, 17]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [8, 19]⟩, ⟨.and, [2, 26]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [28, 16]⟩, ⟨.and, [3, 29]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [31, 18]⟩, ⟨.and, [4, 32]⟩, ⟨.or, [14, 19]⟩, ⟨.and, [5, 34]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [36, 18]⟩, ⟨.and, [6, 37]⟩, ⟨.or, [14, 20]⟩, ⟨.and, [7, 39]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [41, 27]⟩, ⟨.or, [42, 30]⟩, ⟨.or, [43, 33]⟩, ⟨.or, [44, 35]⟩, ⟨.or, [45, 38]⟩, ⟨.or, [46, 40]⟩], 47⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 32 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (15103503539490350745 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19770

theorem PEqualNP.Outside.L_meta_19770 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15103503539490350745 : ℕ).testBit (8 * u.val + v.val)) 32) :=
  ⟨PEqualNP.Outside.L_meta_19770.witness, PEqualNP.Outside.L_meta_19770.mono, PEqualNP.Outside.L_meta_19770.small, PEqualNP.Outside.L_meta_19770.rep⟩
