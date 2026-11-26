import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20535

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [11, 14]⟩, ⟨.or, [3, 15]⟩], 16⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 9 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun (u : Fin 3) (v : Fin 5) => (7549 : ℕ).testBit (5 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_20535

theorem PEqualNP.Outside.L_meta_20535 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (7549 : ℕ).testBit (5 * u.val + v.val)) 9) :=
  ⟨PEqualNP.Outside.L_meta_20535.witness, PEqualNP.Outside.L_meta_20535.mono, PEqualNP.Outside.L_meta_20535.small, PEqualNP.Outside.L_meta_20535.rep⟩
