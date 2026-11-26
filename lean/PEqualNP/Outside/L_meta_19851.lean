import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19851

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 14]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [23, 20]⟩, ⟨.and, [0, 24]⟩, ⟨.or, [9, 22]⟩, ⟨.and, [1, 26]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [28, 19]⟩, ⟨.and, [2, 29]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [3, 31]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [33, 18]⟩, ⟨.and, [4, 34]⟩, ⟨.or, [11, 22]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [17, 21]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [25, 27]⟩, ⟨.or, [42, 30]⟩, ⟨.or, [43, 32]⟩, ⟨.or, [44, 35]⟩, ⟨.or, [45, 37]⟩, ⟨.or, [46, 39]⟩, ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 33 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (16558535637132752415 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19851

theorem PEqualNP.Outside.L_meta_19851 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16558535637132752415 : ℕ).testBit (8 * u.val + v.val)) 33) :=
  ⟨PEqualNP.Outside.L_meta_19851.witness, PEqualNP.Outside.L_meta_19851.mono, PEqualNP.Outside.L_meta_19851.small, PEqualNP.Outside.L_meta_19851.rep⟩
