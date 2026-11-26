import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19660_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [10, 9]⟩, ⟨.and, [11, 2]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 2]⟩, ⟨.not, [16]⟩, ⟨.and, [15, 17]⟩, ⟨.or, [14, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19660_aux

theorem PEqualNP.Outside.L_meta_19660 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (15768113 : ℕ).testBit (5 * u.val + v.val)) C) := by
  exact ⟨PEqualNP.Outside.L_meta_19660_aux.circuit, PEqualNP.Outside.L_meta_19660_aux.fan, by decide, by decide +kernel⟩
