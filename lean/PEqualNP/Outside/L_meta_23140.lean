import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23140_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [0, 3]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [6, 10]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.and, [9, 12]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.and, [14, 17]⟩], 18⟩

theorem shape : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23140_aux

theorem PEqualNP.Outside.L_meta_23140 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (13174 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.L_meta_23140_aux.circuit, PEqualNP.Outside.L_meta_23140_aux.shape,
    by decide, by decide +kernel⟩
