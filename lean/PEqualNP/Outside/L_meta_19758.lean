import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19758

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 11]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [21, 17]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [9, 20]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [15, 20]⟩, ⟨.and, [2, 26]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [3, 28]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [30, 18]⟩, ⟨.and, [4, 31]⟩, ⟨.or, [16, 19]⟩, ⟨.and, [5, 33]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [35, 14]⟩, ⟨.or, [36, 15]⟩, ⟨.and, [6, 37]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [7, 39]⟩, ⟨.or, [23, 25]⟩, ⟨.or, [41, 27]⟩, ⟨.or, [42, 29]⟩, ⟨.or, [43, 32]⟩, ⟨.or, [44, 34]⟩, ⟨.or, [45, 38]⟩, ⟨.or, [46, 40]⟩], 47⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 32 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (7413361890700106610 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19758

theorem PEqualNP.Outside.L_meta_19758 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7413361890700106610 : ℕ).testBit (8 * u.val + v.val)) 32) :=
  ⟨PEqualNP.Outside.L_meta_19758.witness, PEqualNP.Outside.L_meta_19758.mono, PEqualNP.Outside.L_meta_19758.small, PEqualNP.Outside.L_meta_19758.rep⟩
