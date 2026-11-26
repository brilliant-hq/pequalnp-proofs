import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20661

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [6, 7]⟩, ⟨.or, [8, 10]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [3, 10]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [15, 14]⟩], 16⟩

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun u v : Fin 5 => (14877696 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_20661

theorem PEqualNP.Outside.L_meta_20661 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (14877696 : ℕ).testBit (5 * u.val + v.val)) 7 :=
  ⟨PEqualNP.Outside.L_meta_20661.circ, PEqualNP.Outside.L_meta_20661.mono, by decide, PEqualNP.Outside.L_meta_20661.rep⟩
