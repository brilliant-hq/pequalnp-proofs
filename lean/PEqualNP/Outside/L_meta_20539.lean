import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20539

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [8, 12]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [3, 15]⟩], 16⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 9 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun (u : Fin 3) (v : Fin 5) => (8061 : ℕ).testBit (5 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_20539

theorem PEqualNP.Outside.L_meta_20539 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (8061 : ℕ).testBit (5 * u.val + v.val)) 9) :=
  ⟨PEqualNP.Outside.L_meta_20539.witness, PEqualNP.Outside.L_meta_20539.mono, PEqualNP.Outside.L_meta_20539.small, PEqualNP.Outside.L_meta_20539.rep⟩
