import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19884

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 11]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [12, 18]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [15, 17]⟩, ⟨.and, [1, 21]⟩, ⟨.or, [12, 16]⟩, ⟨.and, [2, 23]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [25, 14]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [13, 18]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [13, 17]⟩, ⟨.and, [5, 30]⟩, ⟨.or, [13, 16]⟩, ⟨.and, [6, 32]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [34, 12]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [37, 24]⟩, ⟨.or, [38, 27]⟩, ⟨.or, [39, 29]⟩, ⟨.or, [40, 31]⟩, ⟨.or, [41, 33]⟩, ⟨.or, [42, 36]⟩], 43⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 28 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (1885146376704737940 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19884

theorem PEqualNP.Outside.L_meta_19884 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1885146376704737940 : ℕ).testBit (8 * u.val + v.val)) 28) :=
  ⟨PEqualNP.Outside.L_meta_19884.witness, PEqualNP.Outside.L_meta_19884.mono, PEqualNP.Outside.L_meta_19884.small, PEqualNP.Outside.L_meta_19884.rep⟩
