import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19728

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 11]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [21, 12]⟩, ⟨.or, [22, 14]⟩, ⟨.or, [23, 15]⟩, ⟨.and, [0, 24]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [1, 26]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [28, 18]⟩, ⟨.and, [2, 29]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [3, 31]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [33, 18]⟩, ⟨.and, [4, 34]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [38, 20]⟩, ⟨.and, [6, 39]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [41, 19]⟩, ⟨.and, [7, 42]⟩, ⟨.or, [25, 27]⟩, ⟨.or, [44, 30]⟩, ⟨.or, [45, 32]⟩, ⟨.or, [46, 35]⟩, ⟨.or, [47, 37]⟩, ⟨.or, [48, 40]⟩, ⟨.or, [49, 43]⟩], 50⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 35 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (13346266753825361370 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19728

theorem PEqualNP.Outside.L_meta_19728 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13346266753825361370 : ℕ).testBit (8 * u.val + v.val)) 35) :=
  ⟨PEqualNP.Outside.L_meta_19728.witness, PEqualNP.Outside.L_meta_19728.mono, PEqualNP.Outside.L_meta_19728.small, PEqualNP.Outside.L_meta_19728.rep⟩
