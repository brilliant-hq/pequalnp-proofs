import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20458

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [11, 12]⟩], 13⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 6 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun (u : Fin 3) (v : Fin 5) => (235 : ℕ).testBit (5 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_20458

theorem PEqualNP.Outside.L_meta_20458 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (235 : ℕ).testBit (5 * u.val + v.val)) 6) :=
  ⟨PEqualNP.Outside.L_meta_20458.witness, PEqualNP.Outside.L_meta_20458.mono, PEqualNP.Outside.L_meta_20458.small, PEqualNP.Outside.L_meta_20458.rep⟩
