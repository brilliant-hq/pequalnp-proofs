import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19902

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [24, 14]⟩, ⟨.or, [25, 19]⟩, ⟨.and, [1, 26]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [2, 28]⟩, ⟨.or, [17, 21]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [4, 32]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [34, 18]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [37, 19]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [8, 18]⟩, ⟨.or, [40, 19]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [23, 27]⟩, ⟨.or, [43, 29]⟩, ⟨.or, [44, 31]⟩, ⟨.or, [45, 33]⟩, ⟨.or, [46, 36]⟩, ⟨.or, [47, 39]⟩, ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 34 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (17418911685824797215 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19902

theorem PEqualNP.Outside.L_meta_19902 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17418911685824797215 : ℕ).testBit (8 * u.val + v.val)) 34) :=
  ⟨PEqualNP.Outside.L_meta_19902.witness, PEqualNP.Outside.L_meta_19902.mono, PEqualNP.Outside.L_meta_19902.small, PEqualNP.Outside.L_meta_19902.rep⟩
