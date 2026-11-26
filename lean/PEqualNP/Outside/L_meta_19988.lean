import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19988

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [1, 3]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.or, [7, 16]⟩,
    ⟨.or, [2, 17]⟩,
    ⟨.or, [3, 18]⟩,
    ⟨.or, [5, 18]⟩,
    ⟨.or, [1, 19]⟩,
    ⟨.or, [4, 17]⟩,
    ⟨.or, [0, 19]⟩,
    ⟨.or, [6, 16]⟩,
    ⟨.and, [8, 20]⟩,
    ⟨.and, [9, 21]⟩,
    ⟨.and, [10, 22]⟩,
    ⟨.and, [11, 23]⟩,
    ⟨.and, [12, 24]⟩,
    ⟨.and, [13, 25]⟩,
    ⟨.and, [14, 26]⟩,
    ⟨.and, [15, 27]⟩,
    ⟨.or, [28, 29]⟩,
    ⟨.or, [30, 36]⟩,
    ⟨.or, [31, 37]⟩,
    ⟨.or, [32, 38]⟩,
    ⟨.or, [33, 39]⟩,
    ⟨.or, [34, 40]⟩,
    ⟨.or, [35, 41]⟩], 42⟩

theorem allowed : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_19988

theorem PEqualNP.Outside.L_meta_19988 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5882310434002997580 : ℕ).testBit (8 * u.val + v.val)) 27) := by
  exact ⟨PEqualNP.Outside.L_meta_19988.witness, PEqualNP.Outside.L_meta_19988.allowed, by decide, by decide +kernel⟩
