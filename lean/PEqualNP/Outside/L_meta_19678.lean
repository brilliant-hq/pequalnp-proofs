import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19678_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [0, 9]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [1, 12]⟩, ⟨.not, [12]⟩, ⟨.or, [6, 5]⟩, ⟨.and, [14, 10]⟩, ⟨.and, [4, 15]⟩, ⟨.or, [17, 13]⟩, ⟨.or, [16, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19678_aux

theorem PEqualNP.Outside.L_meta_19678 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3687098 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19678_aux.circuit, PEqualNP.Outside.L_meta_19678_aux.fan, by decide, by decide +kernel⟩
