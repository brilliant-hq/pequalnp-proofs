import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19900

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [9, 15]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [14, 18]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [21, 15]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [24, 12]⟩, ⟨.and, [2, 25]⟩, ⟨.or, [8, 18]⟩, ⟨.and, [3, 27]⟩, ⟨.or, [14, 17]⟩, ⟨.and, [4, 29]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [5, 31]⟩, ⟨.or, [8, 16]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [8, 17]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [37, 26]⟩, ⟨.or, [38, 28]⟩, ⟨.or, [39, 30]⟩, ⟨.or, [40, 32]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 36]⟩], 43⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 28 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (973835576939030640 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19900

theorem PEqualNP.Outside.L_meta_19900 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (973835576939030640 : ℕ).testBit (8 * u.val + v.val)) 28) :=
  ⟨PEqualNP.Outside.L_meta_19900.witness, PEqualNP.Outside.L_meta_19900.mono, PEqualNP.Outside.L_meta_19900.small, PEqualNP.Outside.L_meta_19900.rep⟩
