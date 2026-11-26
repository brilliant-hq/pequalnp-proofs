import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19092

private def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [3, 7]⟩, ⟨.not, [8]⟩], 9⟩

end PEqualNP.Outside.L_meta_19092

theorem PEqualNP.Outside.L_meta_19092 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (1911 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19092.witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19092.witness]
  · unfold PEqualNP.Represents.Represents
    decide +kernel
