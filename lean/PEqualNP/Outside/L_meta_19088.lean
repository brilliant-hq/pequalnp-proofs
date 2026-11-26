import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19088

private def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.and, [2, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [3, 9]⟩, ⟨.not, [10]⟩], 11⟩

end PEqualNP.Outside.L_meta_19088

theorem PEqualNP.Outside.L_meta_19088 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (887 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19088.witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19088.witness]
  · unfold PEqualNP.Represents.Represents
    decide +kernel
