import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19105

private def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.and, [1, 4]⟩, ⟨.or, [7, 5]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [7, 6]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [8, 13]⟩, ⟨.not, [14]⟩], 15⟩

end PEqualNP.Outside.L_meta_19105

theorem PEqualNP.Outside.L_meta_19105 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (13807 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19105.witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19105.witness]
  · unfold PEqualNP.Represents.Represents
    decide +kernel
