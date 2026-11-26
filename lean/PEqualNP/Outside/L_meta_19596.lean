import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19596_aux

def circuit : Circuit :=
  ⟨[⟨.or, [0, 9]⟩,
    ⟨.and, [1, 5]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.or, [5, 8]⟩,
    ⟨.or, [4, 13]⟩,
    ⟨.and, [10, 14]⟩,
    ⟨.not, [15]⟩,
    ⟨.and, [12, 16]⟩,
    ⟨.or, [11, 17]⟩], 18⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19596_aux

open PEqualNP.Outside.L_meta_19596_aux in
theorem PEqualNP.Outside.L_meta_19596 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16269878 : ℕ).testBit (5 * u.val + v.val)) C) := by
  exact ⟨circuit, fan, by decide, by decide +kernel⟩
