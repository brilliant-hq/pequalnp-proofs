import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19237_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [3, 0]⟩, ⟨.and, [4, 9]⟩, ⟨.not, [10]⟩, ⟨.and, [8, 11]⟩], 12⟩

private theorem legal : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19237_aux

open PEqualNP.Outside.L_meta_19237_aux

theorem PEqualNP.Outside.L_meta_19237 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (286 : ℕ).testBit (4 * u.val + v.val)) C) := by
  exact ⟨circuit, legal, by decide, by decide +kernel⟩
