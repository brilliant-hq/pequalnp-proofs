import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19769

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [9, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [8, 17]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [21, 14]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [10, 16]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [10, 17]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [13, 18]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [10, 18]⟩, ⟨.and, [5, 30]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [32, 15]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [11, 16]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [37, 25]⟩, ⟨.or, [38, 27]⟩, ⟨.or, [39, 29]⟩, ⟨.or, [40, 31]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 36]⟩], 43⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 28 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (1910587134026600745 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19769

theorem PEqualNP.Outside.L_meta_19769 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1910587134026600745 : ℕ).testBit (8 * u.val + v.val)) 28) :=
  ⟨PEqualNP.Outside.L_meta_19769.witness, PEqualNP.Outside.L_meta_19769.mono, PEqualNP.Outside.L_meta_19769.small, PEqualNP.Outside.L_meta_19769.rep⟩
