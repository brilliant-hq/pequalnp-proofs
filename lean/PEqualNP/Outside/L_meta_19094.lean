import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19094

private def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [3, 7]⟩, ⟨.not, [8]⟩, ⟨.or, [0, 9]⟩], 10⟩

end PEqualNP.Outside.L_meta_19094

theorem PEqualNP.Outside.L_meta_19094 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (1919 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19094.witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19094.witness]
  · unfold PEqualNP.Represents.Represents
    decide +kernel
