import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20524

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [8, 15]⟩, ⟨.or, [12, 16]⟩], 17⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 10 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun (u : Fin 3) (v : Fin 5) => (3518 : ℕ).testBit (5 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_20524

theorem PEqualNP.Outside.L_meta_20524 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (3518 : ℕ).testBit (5 * u.val + v.val)) 10) :=
  ⟨PEqualNP.Outside.L_meta_20524.witness, PEqualNP.Outside.L_meta_20524.mono, PEqualNP.Outside.L_meta_20524.small, PEqualNP.Outside.L_meta_20524.rep⟩
