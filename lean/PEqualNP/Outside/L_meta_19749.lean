import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19749

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [15, 18]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [22, 20]⟩, ⟨.and, [0, 23]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [27, 19]⟩, ⟨.and, [2, 28]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [32, 13]⟩, ⟨.or, [33, 16]⟩, ⟨.and, [4, 34]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [38, 21]⟩, ⟨.and, [6, 39]⟩, ⟨.or, [17, 21]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [24, 26]⟩, ⟨.or, [43, 29]⟩, ⟨.or, [44, 31]⟩, ⟨.or, [45, 35]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 40]⟩, ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 34 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (17069659891248394590 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19749

theorem PEqualNP.Outside.L_meta_19749 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17069659891248394590 : ℕ).testBit (8 * u.val + v.val)) 34) :=
  ⟨PEqualNP.Outside.L_meta_19749.witness, PEqualNP.Outside.L_meta_19749.mono, PEqualNP.Outside.L_meta_19749.small, PEqualNP.Outside.L_meta_19749.rep⟩
