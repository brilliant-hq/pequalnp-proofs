import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19523_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [4, 5]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [3, 15]⟩, ⟨.and, [13, 16]⟩, ⟨.not, [17]⟩, ⟨.and, [14, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19523_aux

theorem PEqualNP.Outside.L_meta_19523 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (12060214 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19523_aux.circuit, PEqualNP.Outside.L_meta_19523_aux.fan, by decide, by decide +kernel⟩
