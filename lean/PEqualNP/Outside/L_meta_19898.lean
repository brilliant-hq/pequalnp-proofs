import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19898

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 11]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [9, 19]⟩, ⟨.and, [0, 20]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [22, 11]⟩, ⟨.or, [23, 15]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [26, 17]⟩, ⟨.and, [2, 27]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [29, 18]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [4, 32]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [34, 16]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [37, 17]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [15, 19]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [21, 25]⟩, ⟨.or, [42, 28]⟩, ⟨.or, [43, 31]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [45, 36]⟩, ⟨.or, [46, 39]⟩, ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 33 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (14516395958052687435 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19898

theorem PEqualNP.Outside.L_meta_19898 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14516395958052687435 : ℕ).testBit (8 * u.val + v.val)) 33) :=
  ⟨PEqualNP.Outside.L_meta_19898.witness, PEqualNP.Outside.L_meta_19898.mono, PEqualNP.Outside.L_meta_19898.small, PEqualNP.Outside.L_meta_19898.rep⟩
