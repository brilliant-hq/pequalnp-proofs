import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19767

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 13]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [20, 16]⟩, ⟨.and, [0, 21]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [1, 23]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [25, 19]⟩, ⟨.and, [2, 26]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [3, 28]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [4, 30]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [32, 17]⟩, ⟨.and, [5, 33]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [35, 17]⟩, ⟨.and, [6, 36]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [38, 16]⟩, ⟨.and, [7, 39]⟩, ⟨.or, [22, 24]⟩, ⟨.or, [41, 27]⟩, ⟨.or, [42, 29]⟩, ⟨.or, [43, 31]⟩, ⟨.or, [44, 34]⟩, ⟨.or, [45, 37]⟩, ⟨.or, [46, 40]⟩], 47⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 32 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (7184026854491237685 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19767

theorem PEqualNP.Outside.L_meta_19767 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7184026854491237685 : ℕ).testBit (8 * u.val + v.val)) 32) :=
  ⟨PEqualNP.Outside.L_meta_19767.witness, PEqualNP.Outside.L_meta_19767.mono, PEqualNP.Outside.L_meta_19767.small, PEqualNP.Outside.L_meta_19767.rep⟩
