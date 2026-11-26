import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19716

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 10]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [19, 15]⟩, ⟨.and, [0, 20]⟩, ⟨.or, [13, 17]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [10, 18]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [12, 17]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [28, 15]⟩, ⟨.and, [4, 29]⟩, ⟨.or, [9, 16]⟩, ⟨.and, [5, 31]⟩, ⟨.or, [13, 18]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [15, 16]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [21, 23]⟩, ⟨.or, [37, 25]⟩, ⟨.or, [38, 27]⟩, ⟨.or, [39, 30]⟩, ⟨.or, [40, 32]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 36]⟩], 43⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 28 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (9599430892109718240 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19716

theorem PEqualNP.Outside.L_meta_19716 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9599430892109718240 : ℕ).testBit (8 * u.val + v.val)) 28) :=
  ⟨PEqualNP.Outside.L_meta_19716.witness, PEqualNP.Outside.L_meta_19716.mono, PEqualNP.Outside.L_meta_19716.small, PEqualNP.Outside.L_meta_19716.rep⟩
