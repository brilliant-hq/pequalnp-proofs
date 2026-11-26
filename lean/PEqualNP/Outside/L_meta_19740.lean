import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19740

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 14]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [22, 17]⟩, ⟨.and, [0, 23]⟩, ⟨.or, [8, 20]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [27, 13]⟩, ⟨.or, [28, 16]⟩, ⟨.and, [2, 29]⟩, ⟨.or, [15, 20]⟩, ⟨.and, [3, 31]⟩, ⟨.or, [11, 21]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [9, 20]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [14, 18]⟩, ⟨.or, [37, 19]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [12, 21]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [24, 26]⟩, ⟨.or, [42, 30]⟩, ⟨.or, [43, 32]⟩, ⟨.or, [44, 34]⟩, ⟨.or, [45, 36]⟩, ⟨.or, [46, 39]⟩, ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 33 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (15272338331126939085 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19740

theorem PEqualNP.Outside.L_meta_19740 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15272338331126939085 : ℕ).testBit (8 * u.val + v.val)) 33) :=
  ⟨PEqualNP.Outside.L_meta_19740.witness, PEqualNP.Outside.L_meta_19740.mono, PEqualNP.Outside.L_meta_19740.small, PEqualNP.Outside.L_meta_19740.rep⟩
