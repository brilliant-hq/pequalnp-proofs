import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19933

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 10]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [9, 19]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [22, 18]⟩, ⟨.and, [0, 23]⟩, ⟨.or, [15, 21]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [27, 20]⟩, ⟨.and, [2, 28]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [11, 21]⟩, ⟨.and, [4, 32]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [34, 12]⟩, ⟨.or, [35, 18]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [24, 26]⟩, ⟨.or, [42, 29]⟩, ⟨.or, [43, 31]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [45, 37]⟩, ⟨.or, [46, 39]⟩, ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 33 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (13467367414173452220 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19933

theorem PEqualNP.Outside.L_meta_19933 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13467367414173452220 : ℕ).testBit (8 * u.val + v.val)) 33) :=
  ⟨PEqualNP.Outside.L_meta_19933.witness, PEqualNP.Outside.L_meta_19933.mono, PEqualNP.Outside.L_meta_19933.small, PEqualNP.Outside.L_meta_19933.rep⟩
