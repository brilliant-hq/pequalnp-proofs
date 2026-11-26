import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19441_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [5, 6]⟩, ⟨.or, [10, 0]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [2, 11]⟩, ⟨.and, [14, 15]⟩, ⟨.not, [16]⟩, ⟨.and, [13, 17]⟩, ⟨.or, [12, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19441_aux

theorem PEqualNP.Outside.L_meta_19441 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7580827 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19441_aux.circuit, PEqualNP.Outside.L_meta_19441_aux.fan, by decide, by decide +kernel⟩
