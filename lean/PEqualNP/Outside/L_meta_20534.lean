import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20534

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [8, 14]⟩, ⟨.and, [15, 16]⟩], 17⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 10 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun (u : Fin 3) (v : Fin 5) => (7548 : ℕ).testBit (5 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_20534

theorem PEqualNP.Outside.L_meta_20534 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (7548 : ℕ).testBit (5 * u.val + v.val)) 10) :=
  ⟨PEqualNP.Outside.L_meta_20534.witness, PEqualNP.Outside.L_meta_20534.mono, PEqualNP.Outside.L_meta_20534.small, PEqualNP.Outside.L_meta_20534.rep⟩
