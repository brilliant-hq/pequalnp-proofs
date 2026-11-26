import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19314_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.and, [4, 8]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [12, 0]⟩, ⟨.not, [13]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [15, 0]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19314_aux

theorem PEqualNP.Outside.L_meta_19314 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7712116 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19314_aux.circuit, PEqualNP.Outside.L_meta_19314_aux.fan, by decide, by decide +kernel⟩
