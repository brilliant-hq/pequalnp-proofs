import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19734

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 10]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [18, 15]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [13, 16]⟩, ⟨.and, [1, 21]⟩, ⟨.or, [9, 16]⟩, ⟨.and, [2, 23]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [25, 15]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [9, 17]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [30, 15]⟩, ⟨.and, [5, 31]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [33, 13]⟩, ⟨.and, [6, 34]⟩, ⟨.or, [12, 17]⟩, ⟨.and, [7, 36]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [38, 24]⟩, ⟨.or, [39, 27]⟩, ⟨.or, [40, 29]⟩, ⟨.or, [41, 32]⟩, ⟨.or, [42, 35]⟩, ⟨.or, [43, 37]⟩], 44⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 29 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (6355890012357600705 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19734

theorem PEqualNP.Outside.L_meta_19734 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6355890012357600705 : ℕ).testBit (8 * u.val + v.val)) 29) :=
  ⟨PEqualNP.Outside.L_meta_19734.witness, PEqualNP.Outside.L_meta_19734.mono, PEqualNP.Outside.L_meta_19734.small, PEqualNP.Outside.L_meta_19734.rep⟩
