import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19443_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [6, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [10, 14]⟩, ⟨.not, [15]⟩, ⟨.or, [12, 16]⟩, ⟨.and, [5, 4]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19443_aux

theorem PEqualNP.Outside.L_meta_19443 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7641913 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19443_aux.circuit, PEqualNP.Outside.L_meta_19443_aux.fan, by decide, by decide +kernel⟩
