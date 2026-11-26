import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20692

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [5, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [16, 15]⟩], 17⟩

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun u v : Fin 5 => (15795200 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_20692

theorem PEqualNP.Outside.L_meta_20692 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15795200 : ℕ).testBit (5 * u.val + v.val)) 8 :=
  ⟨PEqualNP.Outside.L_meta_20692.circ, PEqualNP.Outside.L_meta_20692.mono, by decide, PEqualNP.Outside.L_meta_20692.rep⟩
