import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19904

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 14]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [20, 16]⟩, ⟨.and, [0, 21]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [23, 17]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [26, 16]⟩, ⟨.and, [2, 27]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [3, 29]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [4, 31]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [33, 17]⟩, ⟨.and, [5, 34]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [6, 36]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [38, 19]⟩, ⟨.and, [7, 39]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [41, 28]⟩, ⟨.or, [42, 30]⟩, ⟨.or, [43, 32]⟩, ⟨.or, [44, 35]⟩, ⟨.or, [45, 37]⟩, ⟨.or, [46, 40]⟩], 47⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 32 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (11770628888104126035 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19904

theorem PEqualNP.Outside.L_meta_19904 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11770628888104126035 : ℕ).testBit (8 * u.val + v.val)) 32) :=
  ⟨PEqualNP.Outside.L_meta_19904.witness, PEqualNP.Outside.L_meta_19904.mono, PEqualNP.Outside.L_meta_19904.small, PEqualNP.Outside.L_meta_19904.rep⟩
