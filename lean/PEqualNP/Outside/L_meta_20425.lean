import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20425

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [10, 13]⟩], 14⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 8 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun (u : Fin 3) (v : Fin 4) => (990 : ℕ).testBit (4 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_20425

theorem PEqualNP.Outside.L_meta_20425 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (990 : ℕ).testBit (4 * u.val + v.val)) 8) :=
  ⟨PEqualNP.Outside.L_meta_20425.witness, PEqualNP.Outside.L_meta_20425.mono, PEqualNP.Outside.L_meta_20425.small, PEqualNP.Outside.L_meta_20425.rep⟩
