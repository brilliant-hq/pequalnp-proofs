import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19934

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 9]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [10, 16]⟩, ⟨.and, [0, 18]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [20, 13]⟩, ⟨.and, [1, 21]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [23, 15]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [15, 16]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [28, 14]⟩, ⟨.and, [4, 29]⟩, ⟨.or, [15, 17]⟩, ⟨.and, [5, 31]⟩, ⟨.or, [11, 17]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [35, 13]⟩, ⟨.and, [7, 36]⟩, ⟨.or, [19, 22]⟩, ⟨.or, [38, 25]⟩, ⟨.or, [39, 27]⟩, ⟨.or, [40, 30]⟩, ⟨.or, [41, 32]⟩, ⟨.or, [42, 34]⟩, ⟨.or, [43, 37]⟩], 44⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 29 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (3051417864780919815 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19934

theorem PEqualNP.Outside.L_meta_19934 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3051417864780919815 : ℕ).testBit (8 * u.val + v.val)) 29) :=
  ⟨PEqualNP.Outside.L_meta_19934.witness, PEqualNP.Outside.L_meta_19934.mono, PEqualNP.Outside.L_meta_19934.small, PEqualNP.Outside.L_meta_19934.rep⟩
