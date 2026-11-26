import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20462_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [12, 13]⟩], 14⟩

theorem fan : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_20462_aux

theorem PEqualNP.Outside.L_meta_20462 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (503 : ℕ).testBit (5 * u.val + v.val)) 7 := by
  exact ⟨PEqualNP.Outside.L_meta_20462_aux.circuit, PEqualNP.Outside.L_meta_20462_aux.fan, by decide, by decide +kernel⟩
