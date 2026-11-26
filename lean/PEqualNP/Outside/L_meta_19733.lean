import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19733

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 9]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [14, 18]⟩, ⟨.or, [17, 21]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [9, 18]⟩, ⟨.or, [26, 19]⟩, ⟨.and, [2, 27]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [29, 19]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [4, 32]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [34, 17]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [37, 19]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [40, 21]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [23, 25]⟩, ⟨.or, [43, 28]⟩, ⟨.or, [44, 31]⟩, ⟨.or, [45, 33]⟩, ⟨.or, [46, 36]⟩, ⟨.or, [47, 39]⟩, ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 34 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (17388182210000334840 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19733

theorem PEqualNP.Outside.L_meta_19733 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17388182210000334840 : ℕ).testBit (8 * u.val + v.val)) 34) :=
  ⟨PEqualNP.Outside.L_meta_19733.witness, PEqualNP.Outside.L_meta_19733.mono, PEqualNP.Outside.L_meta_19733.small, PEqualNP.Outside.L_meta_19733.rep⟩
