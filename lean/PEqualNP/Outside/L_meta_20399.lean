import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20399

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [10, 11]⟩], 12⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 6 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun (u : Fin 3) (v : Fin 4) => (123 : ℕ).testBit (4 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_20399

theorem PEqualNP.Outside.L_meta_20399 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (123 : ℕ).testBit (4 * u.val + v.val)) 6) :=
  ⟨PEqualNP.Outside.L_meta_20399.witness, PEqualNP.Outside.L_meta_20399.mono, PEqualNP.Outside.L_meta_20399.small, PEqualNP.Outside.L_meta_20399.rep⟩
