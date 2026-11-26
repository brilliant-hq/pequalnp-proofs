import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19790

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 10]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [22, 13]⟩, ⟨.or, [23, 18]⟩, ⟨.and, [0, 24]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [26, 18]⟩, ⟨.and, [1, 27]⟩, ⟨.or, [15, 21]⟩, ⟨.and, [2, 29]⟩, ⟨.or, [10, 18]⟩, ⟨.or, [31, 19]⟩, ⟨.and, [3, 32]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [34, 17]⟩, ⟨.and, [4, 35]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [5, 37]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [6, 39]⟩, ⟨.or, [14, 21]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [25, 28]⟩, ⟨.or, [43, 30]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [45, 36]⟩, ⟨.or, [46, 38]⟩, ⟨.or, [47, 40]⟩, ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 34 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (8851041321372796905 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19790

theorem PEqualNP.Outside.L_meta_19790 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8851041321372796905 : ℕ).testBit (8 * u.val + v.val)) 34) :=
  ⟨PEqualNP.Outside.L_meta_19790.witness, PEqualNP.Outside.L_meta_19790.mono, PEqualNP.Outside.L_meta_19790.small, PEqualNP.Outside.L_meta_19790.rep⟩
