import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20540

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [8, 15]⟩], 16⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 9 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun (u : Fin 3) (v : Fin 5) => (16123 : ℕ).testBit (5 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_20540

theorem PEqualNP.Outside.L_meta_20540 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (16123 : ℕ).testBit (5 * u.val + v.val)) 9) :=
  ⟨PEqualNP.Outside.L_meta_20540.witness, PEqualNP.Outside.L_meta_20540.mono, PEqualNP.Outside.L_meta_20540.small, PEqualNP.Outside.L_meta_20540.rep⟩
