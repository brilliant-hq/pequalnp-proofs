import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19208

private def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.and, [1, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [3, 7]⟩, ⟨.not, [10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [8, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_19208

theorem PEqualNP.Outside.L_meta_19208 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (311 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19208.witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19208.witness]
  · unfold PEqualNP.Represents.Represents
    decide +kernel
