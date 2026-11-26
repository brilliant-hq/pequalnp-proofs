import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20520

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [10, 14]⟩, ⟨.and, [13, 15]⟩], 16⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 9 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun (u : Fin 3) (v : Fin 5) => (3510 : ℕ).testBit (5 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_20520

theorem PEqualNP.Outside.L_meta_20520 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (3510 : ℕ).testBit (5 * u.val + v.val)) 9) :=
  ⟨PEqualNP.Outside.L_meta_20520.witness, PEqualNP.Outside.L_meta_20520.mono, PEqualNP.Outside.L_meta_20520.small, PEqualNP.Outside.L_meta_20520.rep⟩
