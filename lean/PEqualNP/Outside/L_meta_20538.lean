import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20538

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [8, 11]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 9 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun (u : Fin 3) (v : Fin 5) => (7998 : ℕ).testBit (5 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_20538

theorem PEqualNP.Outside.L_meta_20538 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (7998 : ℕ).testBit (5 * u.val + v.val)) 9) :=
  ⟨PEqualNP.Outside.L_meta_20538.witness, PEqualNP.Outside.L_meta_20538.mono, PEqualNP.Outside.L_meta_20538.small, PEqualNP.Outside.L_meta_20538.rep⟩
