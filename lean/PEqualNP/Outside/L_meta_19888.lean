import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19888

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 10]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [0, 20]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [22, 12]⟩, ⟨.or, [23, 15]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [26, 16]⟩, ⟨.and, [2, 27]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [29, 16]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [4, 32]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [34, 17]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [6, 37]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [39, 19]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [21, 25]⟩, ⟨.or, [42, 28]⟩, ⟨.or, [43, 31]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [45, 36]⟩, ⟨.or, [46, 38]⟩, ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 33 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (14500150567228511850 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19888

theorem PEqualNP.Outside.L_meta_19888 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14500150567228511850 : ℕ).testBit (8 * u.val + v.val)) 33) :=
  ⟨PEqualNP.Outside.L_meta_19888.witness, PEqualNP.Outside.L_meta_19888.mono, PEqualNP.Outside.L_meta_19888.small, PEqualNP.Outside.L_meta_19888.rep⟩
