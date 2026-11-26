import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19936

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 15]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [9, 18]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [22, 21]⟩, ⟨.and, [0, 23]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [25, 21]⟩, ⟨.and, [1, 26]⟩, ⟨.or, [16, 19]⟩, ⟨.and, [2, 28]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [30, 20]⟩, ⟨.and, [3, 31]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [37, 18]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [40, 19]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [24, 27]⟩, ⟨.or, [43, 29]⟩, ⟨.or, [44, 32]⟩, ⟨.or, [45, 34]⟩, ⟨.or, [46, 36]⟩, ⟨.or, [47, 39]⟩, ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 34 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (6839164070987673195 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19936

theorem PEqualNP.Outside.L_meta_19936 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6839164070987673195 : ℕ).testBit (8 * u.val + v.val)) 34) :=
  ⟨PEqualNP.Outside.L_meta_19936.witness, PEqualNP.Outside.L_meta_19936.mono, PEqualNP.Outside.L_meta_19936.small, PEqualNP.Outside.L_meta_19936.rep⟩
