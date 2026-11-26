import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19713

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [9, 14]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [21, 20]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [24, 20]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [2, 27]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [29, 16]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [32, 17]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [6, 37]⟩, ⟨.or, [16, 19]⟩, ⟨.and, [7, 39]⟩, ⟨.or, [23, 26]⟩, ⟨.or, [41, 28]⟩, ⟨.or, [42, 31]⟩, ⟨.or, [43, 34]⟩, ⟨.or, [44, 36]⟩, ⟨.or, [45, 38]⟩, ⟨.or, [46, 40]⟩], 47⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 32 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (5420442459739364580 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19713

theorem PEqualNP.Outside.L_meta_19713 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5420442459739364580 : ℕ).testBit (8 * u.val + v.val)) 32) :=
  ⟨PEqualNP.Outside.L_meta_19713.witness, PEqualNP.Outside.L_meta_19713.mono, PEqualNP.Outside.L_meta_19713.small, PEqualNP.Outside.L_meta_19713.rep⟩
