import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19708_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [0, 13]⟩, ⟨.not, [14]⟩, ⟨.and, [15, 16]⟩], 17⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19708_aux

theorem PEqualNP.Outside.L_meta_19708 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7572604 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19708_aux.circuit, PEqualNP.Outside.L_meta_19708_aux.fan, by decide, by decide +kernel⟩
