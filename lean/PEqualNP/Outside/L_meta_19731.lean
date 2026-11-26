import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19731

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 10]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [13, 18]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [16, 21]⟩, ⟨.and, [2, 26]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [28, 19]⟩, ⟨.and, [3, 29]⟩, ⟨.or, [8, 17]⟩, ⟨.or, [31, 19]⟩, ⟨.and, [4, 32]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [34, 17]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [37, 15]⟩, ⟨.or, [38, 19]⟩, ⟨.and, [6, 39]⟩, ⟨.or, [17, 21]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [23, 25]⟩, ⟨.or, [43, 27]⟩, ⟨.or, [44, 30]⟩, ⟨.or, [45, 33]⟩, ⟨.or, [46, 36]⟩, ⟨.or, [47, 40]⟩, ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 34 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (16914613873039728090 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19731

theorem PEqualNP.Outside.L_meta_19731 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16914613873039728090 : ℕ).testBit (8 * u.val + v.val)) 34) :=
  ⟨PEqualNP.Outside.L_meta_19731.witness, PEqualNP.Outside.L_meta_19731.mono, PEqualNP.Outside.L_meta_19731.small, PEqualNP.Outside.L_meta_19731.rep⟩
