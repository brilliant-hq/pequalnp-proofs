import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19724

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [16, 19]⟩, ⟨.and, [0, 21]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [23, 16]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [26, 13]⟩, ⟨.or, [27, 15]⟩, ⟨.and, [2, 28]⟩, ⟨.or, [9, 20]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [32, 17]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [6, 37]⟩, ⟨.or, [10, 20]⟩, ⟨.and, [7, 39]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [41, 29]⟩, ⟨.or, [42, 31]⟩, ⟨.or, [43, 34]⟩, ⟨.or, [44, 36]⟩, ⟨.or, [45, 38]⟩, ⟨.or, [46, 40]⟩], 47⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 32 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (7837978282315423185 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19724

theorem PEqualNP.Outside.L_meta_19724 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7837978282315423185 : ℕ).testBit (8 * u.val + v.val)) 32) :=
  ⟨PEqualNP.Outside.L_meta_19724.witness, PEqualNP.Outside.L_meta_19724.mono, PEqualNP.Outside.L_meta_19724.small, PEqualNP.Outside.L_meta_19724.rep⟩
