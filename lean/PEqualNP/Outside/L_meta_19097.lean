import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19097

private def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [1, 7]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.not, [11]⟩], 12⟩

end PEqualNP.Outside.L_meta_19097

theorem PEqualNP.Outside.L_meta_19097 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (1983 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19097.witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19097.witness]
  · unfold PEqualNP.Represents.Represents
    decide +kernel
