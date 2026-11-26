import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19712

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 11]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [12, 18]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [10, 17]⟩, ⟨.and, [1, 21]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [23, 15]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [12, 16]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [15, 17]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [11, 18]⟩, ⟨.and, [5, 30]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [32, 15]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [9, 16]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [37, 25]⟩, ⟨.or, [38, 27]⟩, ⟨.or, [39, 29]⟩, ⟨.or, [40, 31]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 36]⟩], 43⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 28 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (838035264769107540 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19712

theorem PEqualNP.Outside.L_meta_19712 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (838035264769107540 : ℕ).testBit (8 * u.val + v.val)) 28) :=
  ⟨PEqualNP.Outside.L_meta_19712.witness, PEqualNP.Outside.L_meta_19712.mono, PEqualNP.Outside.L_meta_19712.small, PEqualNP.Outside.L_meta_19712.rep⟩
