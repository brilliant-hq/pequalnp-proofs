import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19089

private def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.not, [7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [3, 6]⟩, ⟨.not, [10]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [9, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_19089

theorem PEqualNP.Outside.L_meta_19089 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (891 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19089.witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19089.witness]
  · unfold PEqualNP.Represents.Represents
    decide +kernel
