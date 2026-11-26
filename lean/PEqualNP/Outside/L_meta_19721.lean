import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19721

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [9, 15]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [12, 22]⟩, ⟨.and, [0, 23]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [17, 21]⟩, ⟨.and, [2, 27]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [29, 15]⟩, ⟨.or, [30, 19]⟩, ⟨.and, [3, 31]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [8, 22]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [6, 37]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [39, 13]⟩, ⟨.or, [40, 19]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [24, 26]⟩, ⟨.or, [43, 28]⟩, ⟨.or, [44, 32]⟩, ⟨.or, [45, 34]⟩, ⟨.or, [46, 36]⟩, ⟨.or, [47, 38]⟩, ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 34 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (4319635817910669180 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19721

theorem PEqualNP.Outside.L_meta_19721 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4319635817910669180 : ℕ).testBit (8 * u.val + v.val)) 34) :=
  ⟨PEqualNP.Outside.L_meta_19721.witness, PEqualNP.Outside.L_meta_19721.mono, PEqualNP.Outside.L_meta_19721.small, PEqualNP.Outside.L_meta_19721.rep⟩
