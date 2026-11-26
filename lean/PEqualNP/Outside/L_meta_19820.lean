import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19820_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 13]⟩,
    ⟨.or, [9, 14]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [16, 19]⟩,
    ⟨.and, [0, 20]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.and, [1, 22]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.and, [2, 24]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [26, 16]⟩,
    ⟨.and, [3, 27]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.and, [4, 29]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [31, 18]⟩,
    ⟨.and, [5, 32]⟩,
    ⟨.or, [11, 15]⟩,
    ⟨.or, [34, 17]⟩,
    ⟨.and, [6, 35]⟩,
    ⟨.or, [8, 14]⟩,
    ⟨.or, [37, 19]⟩,
    ⟨.and, [7, 38]⟩,
    ⟨.or, [21, 23]⟩,
    ⟨.or, [40, 25]⟩,
    ⟨.or, [41, 28]⟩,
    ⟨.or, [42, 30]⟩,
    ⟨.or, [43, 33]⟩,
    ⟨.or, [44, 36]⟩,
    ⟨.or, [45, 39]⟩], 46⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19820_aux

theorem PEqualNP.Outside.L_meta_19820 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15116961972522724785 : ℕ).testBit (8 * u.val + v.val)) 31 := by
  exact ⟨PEqualNP.Outside.L_meta_19820_aux.circuit, PEqualNP.Outside.L_meta_19820_aux.mono,
    by decide, by decide +kernel⟩
