import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19394

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [1, 6]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [18, 19]⟩], 20⟩

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun u v : Fin 5 => (3675834 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_19394

theorem PEqualNP.Outside.L_meta_19394 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3675834 : ℕ).testBit (5 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_19394.circ, PEqualNP.Outside.L_meta_19394.mono, by decide, PEqualNP.Outside.L_meta_19394.rep⟩
