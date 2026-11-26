import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19783

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 9]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [14, 18]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [13, 17]⟩, ⟨.and, [1, 21]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [2, 23]⟩, ⟨.or, [11, 17]⟩, ⟨.and, [3, 25]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [27, 15]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [9, 18]⟩, ⟨.and, [5, 30]⟩, ⟨.or, [13, 16]⟩, ⟨.and, [6, 32]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [34, 14]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [37, 24]⟩, ⟨.or, [38, 26]⟩, ⟨.or, [39, 29]⟩, ⟨.or, [40, 31]⟩, ⟨.or, [41, 33]⟩, ⟨.or, [42, 36]⟩], 43⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 28 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (8080454460742251720 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19783

theorem PEqualNP.Outside.L_meta_19783 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8080454460742251720 : ℕ).testBit (8 * u.val + v.val)) 28) :=
  ⟨PEqualNP.Outside.L_meta_19783.witness, PEqualNP.Outside.L_meta_19783.mono, PEqualNP.Outside.L_meta_19783.small, PEqualNP.Outside.L_meta_19783.rep⟩
