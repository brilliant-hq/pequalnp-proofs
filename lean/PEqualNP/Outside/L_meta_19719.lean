import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19719

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 11]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [13, 17]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [9, 18]⟩, ⟨.and, [1, 21]⟩, ⟨.or, [10, 17]⟩, ⟨.and, [2, 23]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [25, 13]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [10, 18]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [12, 16]⟩, ⟨.and, [5, 30]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [32, 14]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [15, 16]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [37, 24]⟩, ⟨.or, [38, 27]⟩, ⟨.or, [39, 29]⟩, ⟨.or, [40, 31]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 36]⟩], 43⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 28 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (9901191629971542690 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19719

theorem PEqualNP.Outside.L_meta_19719 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9901191629971542690 : ℕ).testBit (8 * u.val + v.val)) 28) :=
  ⟨PEqualNP.Outside.L_meta_19719.witness, PEqualNP.Outside.L_meta_19719.mono, PEqualNP.Outside.L_meta_19719.small, PEqualNP.Outside.L_meta_19719.rep⟩
