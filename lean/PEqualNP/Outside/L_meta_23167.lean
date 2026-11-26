import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23167_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [8, 12]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [0, 14]⟩, ⟨.or, [9, 16]⟩, ⟨.and, [15, 17]⟩], 18⟩

theorem fan : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23167_aux

theorem PEqualNP.Outside.L_meta_23167 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30460 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨PEqualNP.Outside.L_meta_23167_aux.circuit, PEqualNP.Outside.L_meta_23167_aux.fan, by decide, by decide +kernel⟩
