import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19889

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [9, 10]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [8, 18]⟩, ⟨.or, [14, 18]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [24, 17]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [2, 27]⟩, ⟨.or, [16, 21]⟩, ⟨.and, [3, 29]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [31, 19]⟩, ⟨.and, [4, 32]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [34, 15]⟩, ⟨.or, [35, 19]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [17, 21]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [40, 19]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [23, 26]⟩, ⟨.or, [43, 28]⟩, ⟨.or, [44, 30]⟩, ⟨.or, [45, 33]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 39]⟩, ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 34 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (6627281390824537785 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19889

theorem PEqualNP.Outside.L_meta_19889 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6627281390824537785 : ℕ).testBit (8 * u.val + v.val)) 34) :=
  ⟨PEqualNP.Outside.L_meta_19889.witness, PEqualNP.Outside.L_meta_19889.mono, PEqualNP.Outside.L_meta_19889.small, PEqualNP.Outside.L_meta_19889.rep⟩
