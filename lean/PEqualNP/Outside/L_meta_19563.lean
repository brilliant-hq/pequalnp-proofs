import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19563_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.and, [0, 8]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [7, 14]⟩, ⟨.not, [12]⟩, ⟨.or, [15, 16]⟩, ⟨.and, [13, 17]⟩], 18⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19563_aux

theorem PEqualNP.Outside.L_meta_19563 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24151086 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19563_aux.circuit, PEqualNP.Outside.L_meta_19563_aux.fan, by decide, by decide +kernel⟩
