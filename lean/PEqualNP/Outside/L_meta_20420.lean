import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20420

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [8, 12]⟩, ⟨.and, [11, 13]⟩], 14⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 8 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun (u : Fin 3) (v : Fin 4) => (862 : ℕ).testBit (4 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_20420

theorem PEqualNP.Outside.L_meta_20420 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (862 : ℕ).testBit (4 * u.val + v.val)) 8) :=
  ⟨PEqualNP.Outside.L_meta_20420.witness, PEqualNP.Outside.L_meta_20420.mono, PEqualNP.Outside.L_meta_20420.small, PEqualNP.Outside.L_meta_20420.rep⟩
