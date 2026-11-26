import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19766

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 10]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [14, 18]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [0, 23]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [25, 12]⟩, ⟨.or, [26, 19]⟩, ⟨.and, [1, 27]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [2, 29]⟩, ⟨.or, [9, 22]⟩, ⟨.and, [3, 31]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [33, 21]⟩, ⟨.and, [4, 34]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [36, 17]⟩, ⟨.and, [5, 37]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [6, 39]⟩, ⟨.or, [10, 22]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [24, 28]⟩, ⟨.or, [43, 30]⟩, ⟨.or, [44, 32]⟩, ⟨.or, [45, 35]⟩, ⟨.or, [46, 38]⟩, ⟨.or, [47, 40]⟩, ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 34 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (17030148307327572375 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19766

theorem PEqualNP.Outside.L_meta_19766 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17030148307327572375 : ℕ).testBit (8 * u.val + v.val)) 34) :=
  ⟨PEqualNP.Outside.L_meta_19766.witness, PEqualNP.Outside.L_meta_19766.mono, PEqualNP.Outside.L_meta_19766.small, PEqualNP.Outside.L_meta_19766.rep⟩
