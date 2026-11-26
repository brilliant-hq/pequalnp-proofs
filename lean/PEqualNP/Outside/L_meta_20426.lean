import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20426_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[⟨.and, [2, 4]⟩, ⟨.or, [6, 5]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [0, 11]⟩], 12⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_20426_aux

theorem PEqualNP.Outside.L_meta_20426 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (991 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  exact ⟨PEqualNP.Outside.L_meta_20426_aux.circuit, PEqualNP.Outside.L_meta_20426_aux.mono, by decide, by decide +kernel⟩
