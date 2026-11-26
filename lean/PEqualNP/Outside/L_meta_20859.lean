import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20859_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨.or, [0, 6]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [12, 9]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [15, 1]⟩, ⟨.and, [11, 3]⟩, ⟨.and, [16, 14]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem basis : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem correct : PEqualNP.Represents.Represents (fun u v : Fin 5 => (27460641 : ℕ).testBit (5 * u.val + v.val)) witness := by
  unfold PEqualNP.Represents.Represents
  decide +kernel

end PEqualNP.Outside.L_meta_20859_aux

theorem PEqualNP.Outside.L_meta_20859 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (27460641 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨PEqualNP.Outside.L_meta_20859_aux.witness, PEqualNP.Outside.L_meta_20859_aux.basis, by decide,
    PEqualNP.Outside.L_meta_20859_aux.correct⟩
