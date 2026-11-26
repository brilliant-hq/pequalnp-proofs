import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20656

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [5, 6]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [8, 10]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [13, 4]⟩, ⟨.or, [14, 15]⟩], 16⟩

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun u v : Fin 5 => (11770880 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_20656

theorem PEqualNP.Outside.L_meta_20656 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (11770880 : ℕ).testBit (5 * u.val + v.val)) 7 :=
  ⟨PEqualNP.Outside.L_meta_20656.circ, PEqualNP.Outside.L_meta_20656.mono, by decide, PEqualNP.Outside.L_meta_20656.rep⟩
