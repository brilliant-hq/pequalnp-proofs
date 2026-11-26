import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

namespace PEqualNP.Outside.L_meta_19601

def witness : Circuit := ⟨[
  ⟨.or, [1, 2]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.or, [0, 8]⟩,
  ⟨.or, [10, 11]⟩,
  ⟨.or, [10, 12]⟩,
  ⟨.or, [5, 12]⟩,
  ⟨.not, [14]⟩,
  ⟨.and, [13, 15]⟩,
  ⟨.or, [16, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_19601

theorem PEqualNP.Outside.L_meta_19601 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24880422 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C := PEqualNP.Outside.L_meta_19601.witness
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp [C, PEqualNP.Outside.L_meta_19601.witness] at hg
    rcases hg with h|h|h|h|h|h|h|h|h <;> subst g <;> decide
  · decide +kernel
