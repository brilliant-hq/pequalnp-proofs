import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19727

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [10, 13]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [21, 16]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [24, 19]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [27, 20]⟩, ⟨.and, [2, 28]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [32, 18]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [16, 17]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [6, 37]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [39, 19]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [23, 26]⟩, ⟨.or, [42, 29]⟩, ⟨.or, [43, 31]⟩, ⟨.or, [44, 34]⟩, ⟨.or, [45, 36]⟩, ⟨.or, [46, 38]⟩, ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 33 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (10260651070736356020 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19727

theorem PEqualNP.Outside.L_meta_19727 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10260651070736356020 : ℕ).testBit (8 * u.val + v.val)) 33) :=
  ⟨PEqualNP.Outside.L_meta_19727.witness, PEqualNP.Outside.L_meta_19727.mono, PEqualNP.Outside.L_meta_19727.small, PEqualNP.Outside.L_meta_19727.rep⟩
