import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20493

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [11, 15]⟩], 16⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 9 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun (u : Fin 3) (v : Fin 5) => (1495 : ℕ).testBit (5 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_20493

theorem PEqualNP.Outside.L_meta_20493 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (1495 : ℕ).testBit (5 * u.val + v.val)) 9) :=
  ⟨PEqualNP.Outside.L_meta_20493.witness, PEqualNP.Outside.L_meta_20493.mono, PEqualNP.Outside.L_meta_20493.small, PEqualNP.Outside.L_meta_20493.rep⟩
