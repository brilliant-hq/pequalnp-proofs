import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19751

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 12]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [13, 18]⟩, ⟨.or, [17, 21]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [24, 19]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [27, 19]⟩, ⟨.and, [2, 28]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [30, 19]⟩, ⟨.and, [3, 31]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [33, 18]⟩, ⟨.and, [4, 34]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [16, 21]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [40, 20]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [23, 26]⟩, ⟨.or, [43, 29]⟩, ⟨.or, [44, 32]⟩, ⟨.or, [45, 35]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 39]⟩, ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 34 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (10337339320775273190 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19751

theorem PEqualNP.Outside.L_meta_19751 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10337339320775273190 : ℕ).testBit (8 * u.val + v.val)) 34) :=
  ⟨PEqualNP.Outside.L_meta_19751.witness, PEqualNP.Outside.L_meta_19751.mono, PEqualNP.Outside.L_meta_19751.small, PEqualNP.Outside.L_meta_19751.rep⟩
