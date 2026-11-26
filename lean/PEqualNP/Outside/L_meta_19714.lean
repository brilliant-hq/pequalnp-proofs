import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19714

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [9, 13]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [8, 17]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [0, 21]⟩, ⟨.or, [13, 18]⟩, ⟨.or, [23, 19]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [2, 26]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [28, 17]⟩, ⟨.and, [3, 29]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [31, 19]⟩, ⟨.and, [4, 32]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [34, 19]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [37, 11]⟩, ⟨.or, [38, 18]⟩, ⟨.and, [6, 39]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [41, 18]⟩, ⟨.and, [7, 42]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [44, 27]⟩, ⟨.or, [45, 30]⟩, ⟨.or, [46, 33]⟩, ⟨.or, [47, 36]⟩, ⟨.or, [48, 40]⟩, ⟨.or, [49, 43]⟩], 50⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 35 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (17464622044026729945 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19714

theorem PEqualNP.Outside.L_meta_19714 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17464622044026729945 : ℕ).testBit (8 * u.val + v.val)) 35) :=
  ⟨PEqualNP.Outside.L_meta_19714.witness, PEqualNP.Outside.L_meta_19714.mono, PEqualNP.Outside.L_meta_19714.small, PEqualNP.Outside.L_meta_19714.rep⟩
