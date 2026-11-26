import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19735

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [0, 20]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [22, 18]⟩, ⟨.and, [1, 23]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [2, 25]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [27, 16]⟩, ⟨.and, [3, 28]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [30, 16]⟩, ⟨.and, [4, 31]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [5, 33]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [35, 13]⟩, ⟨.or, [36, 14]⟩, ⟨.and, [6, 37]⟩, ⟨.or, [16, 17]⟩, ⟨.and, [7, 39]⟩, ⟨.or, [21, 24]⟩, ⟨.or, [41, 26]⟩, ⟨.or, [42, 29]⟩, ⟨.or, [43, 32]⟩, ⟨.or, [44, 34]⟩, ⟨.or, [45, 38]⟩, ⟨.or, [46, 40]⟩], 47⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 32 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (1110766810026783180 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19735

theorem PEqualNP.Outside.L_meta_19735 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1110766810026783180 : ℕ).testBit (8 * u.val + v.val)) 32) :=
  ⟨PEqualNP.Outside.L_meta_19735.witness, PEqualNP.Outside.L_meta_19735.mono, PEqualNP.Outside.L_meta_19735.small, PEqualNP.Outside.L_meta_19735.rep⟩
