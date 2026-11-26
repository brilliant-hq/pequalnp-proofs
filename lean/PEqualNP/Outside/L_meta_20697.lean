import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20697

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [10, 5]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [15, 16]⟩], 17⟩

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun u v : Fin 5 => (16221216 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_20697

theorem PEqualNP.Outside.L_meta_20697 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (16221216 : ℕ).testBit (5 * u.val + v.val)) 8 :=
  ⟨PEqualNP.Outside.L_meta_20697.circ, PEqualNP.Outside.L_meta_20697.mono, by decide, PEqualNP.Outside.L_meta_20697.rep⟩
