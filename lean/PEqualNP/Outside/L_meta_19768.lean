import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 10]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [24, 19]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [16, 21]⟩, ⟨.and, [2, 27]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [29, 19]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [32, 19]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [8, 17]⟩, ⟨.or, [35, 18]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [40, 20]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [23, 26]⟩, ⟨.or, [43, 28]⟩, ⟨.or, [44, 31]⟩, ⟨.or, [45, 34]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 39]⟩, ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 34 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (5748802764708593400 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19768

theorem PEqualNP.Outside.L_meta_19768 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5748802764708593400 : ℕ).testBit (8 * u.val + v.val)) 34) :=
  ⟨PEqualNP.Outside.L_meta_19768.witness, PEqualNP.Outside.L_meta_19768.mono, PEqualNP.Outside.L_meta_19768.small, PEqualNP.Outside.L_meta_19768.rep⟩
