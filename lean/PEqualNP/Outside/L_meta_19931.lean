import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19931

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 10]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [13, 18]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [26, 19]⟩, ⟨.and, [2, 27]⟩, ⟨.or, [17, 21]⟩, ⟨.and, [3, 29]⟩, ⟨.or, [15, 18]⟩, ⟨.or, [31, 19]⟩, ⟨.and, [4, 32]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [34, 20]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [37, 17]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [8, 17]⟩, ⟨.or, [40, 19]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [23, 25]⟩, ⟨.or, [43, 28]⟩, ⟨.or, [44, 30]⟩, ⟨.or, [45, 33]⟩, ⟨.or, [46, 36]⟩, ⟨.or, [47, 39]⟩, ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 34 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (16399645806311595450 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19931

theorem PEqualNP.Outside.L_meta_19931 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16399645806311595450 : ℕ).testBit (8 * u.val + v.val)) 34) :=
  ⟨PEqualNP.Outside.L_meta_19931.witness, PEqualNP.Outside.L_meta_19931.mono, PEqualNP.Outside.L_meta_19931.small, PEqualNP.Outside.L_meta_19931.rep⟩
