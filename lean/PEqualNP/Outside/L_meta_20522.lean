import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20522

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 9 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun (u : Fin 3) (v : Fin 5) => (3516 : ℕ).testBit (5 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_20522

theorem PEqualNP.Outside.L_meta_20522 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (3516 : ℕ).testBit (5 * u.val + v.val)) 9) :=
  ⟨PEqualNP.Outside.L_meta_20522.witness, PEqualNP.Outside.L_meta_20522.mono, PEqualNP.Outside.L_meta_20522.small, PEqualNP.Outside.L_meta_20522.rep⟩
