import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20647

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [5, 6]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [8, 10]⟩, ⟨.and, [3, 11]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [13, 14]⟩], 15⟩

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun u v : Fin 5 => (11763712 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_20647

theorem PEqualNP.Outside.L_meta_20647 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (11763712 : ℕ).testBit (5 * u.val + v.val)) 6 :=
  ⟨PEqualNP.Outside.L_meta_20647.circ, PEqualNP.Outside.L_meta_20647.mono, by decide, PEqualNP.Outside.L_meta_20647.rep⟩
