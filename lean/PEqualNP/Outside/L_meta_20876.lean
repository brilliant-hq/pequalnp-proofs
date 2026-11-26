import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20876_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [12, 8]⟩, ⟨.and, [10, 5]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [13, 9]⟩, ⟨.and, [4, 16]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [14, 18]⟩], 19⟩

theorem fan : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_20876_aux

theorem PEqualNP.Outside.L_meta_20876 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31930401 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.L_meta_20876_aux.circuit, PEqualNP.Outside.L_meta_20876_aux.fan, by decide, by decide +kernel⟩
