import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20492

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [13, 14]⟩], 15⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 8 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun (u : Fin 3) (v : Fin 5) => (1494 : ℕ).testBit (5 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_20492

theorem PEqualNP.Outside.L_meta_20492 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (1494 : ℕ).testBit (5 * u.val + v.val)) 8) :=
  ⟨PEqualNP.Outside.L_meta_20492.witness, PEqualNP.Outside.L_meta_20492.mono, PEqualNP.Outside.L_meta_20492.small, PEqualNP.Outside.L_meta_20492.rep⟩
