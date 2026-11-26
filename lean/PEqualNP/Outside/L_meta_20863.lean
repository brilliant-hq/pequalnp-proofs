import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20863_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨.or, [7, 2]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [8, 13]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [12, 5]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [15, 16]⟩, ⟨.and, [18, 17]⟩], 19⟩

theorem basis : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem correct : PEqualNP.Represents.Represents (fun u v : Fin 5 => (30280737 : ℕ).testBit (5 * u.val + v.val)) witness := by
  unfold PEqualNP.Represents.Represents
  decide +kernel

end PEqualNP.Outside.L_meta_20863_aux

theorem PEqualNP.Outside.L_meta_20863 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (30280737 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨PEqualNP.Outside.L_meta_20863_aux.witness, PEqualNP.Outside.L_meta_20863_aux.basis, by decide,
    PEqualNP.Outside.L_meta_20863_aux.correct⟩
