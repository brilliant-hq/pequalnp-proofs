import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19115

private def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [2, 7]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [8, 9]⟩, ⟨.not, [10]⟩], 11⟩

end PEqualNP.Outside.L_meta_19115

theorem PEqualNP.Outside.L_meta_19115 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (31743 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19115.witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19115.witness]
  · unfold PEqualNP.Represents.Represents
    decide +kernel
