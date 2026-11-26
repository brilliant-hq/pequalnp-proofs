import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19896

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 15]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [14, 18]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [0, 23]⟩, ⟨.or, [11, 20]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [9, 20]⟩, ⟨.and, [2, 27]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [29, 22]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [16, 22]⟩, ⟨.and, [4, 32]⟩, ⟨.or, [8, 20]⟩, ⟨.and, [5, 34]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [36, 17]⟩, ⟨.and, [6, 37]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [39, 21]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [24, 26]⟩, ⟨.or, [42, 28]⟩, ⟨.or, [43, 31]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [45, 35]⟩, ⟨.or, [46, 38]⟩, ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 33 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (13373287136702659755 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19896

theorem PEqualNP.Outside.L_meta_19896 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13373287136702659755 : ℕ).testBit (8 * u.val + v.val)) 33) :=
  ⟨PEqualNP.Outside.L_meta_19896.witness, PEqualNP.Outside.L_meta_19896.mono, PEqualNP.Outside.L_meta_19896.small, PEqualNP.Outside.L_meta_19896.rep⟩
