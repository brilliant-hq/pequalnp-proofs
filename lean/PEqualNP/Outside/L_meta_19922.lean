import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19922

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 12]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [19, 15]⟩, ⟨.and, [0, 20]⟩, ⟨.or, [10, 17]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [13, 17]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [13, 16]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [11, 16]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [30, 15]⟩, ⟨.and, [5, 31]⟩, ⟨.or, [15, 18]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [14, 18]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [21, 23]⟩, ⟨.or, [37, 25]⟩, ⟨.or, [38, 27]⟩, ⟨.or, [39, 29]⟩, ⟨.or, [40, 32]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 36]⟩], 43⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 28 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (5515944280522376865 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19922

theorem PEqualNP.Outside.L_meta_19922 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5515944280522376865 : ℕ).testBit (8 * u.val + v.val)) 28) :=
  ⟨PEqualNP.Outside.L_meta_19922.witness, PEqualNP.Outside.L_meta_19922.mono, PEqualNP.Outside.L_meta_19922.small, PEqualNP.Outside.L_meta_19922.rep⟩
