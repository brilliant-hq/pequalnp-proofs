import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19779

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 11]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [10, 18]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [12, 19]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [0, 23]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [25, 21]⟩, ⟨.and, [1, 26]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [28, 18]⟩, ⟨.and, [2, 29]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [3, 31]⟩, ⟨.or, [15, 22]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [35, 20]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [13, 22]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [24, 27]⟩, ⟨.or, [42, 30]⟩, ⟨.or, [43, 32]⟩, ⟨.or, [44, 34]⟩, ⟨.or, [45, 37]⟩, ⟨.or, [46, 39]⟩, ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 33 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (17455334905265877990 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19779

theorem PEqualNP.Outside.L_meta_19779 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17455334905265877990 : ℕ).testBit (8 * u.val + v.val)) 33) :=
  ⟨PEqualNP.Outside.L_meta_19779.witness, PEqualNP.Outside.L_meta_19779.mono, PEqualNP.Outside.L_meta_19779.small, PEqualNP.Outside.L_meta_19779.rep⟩
