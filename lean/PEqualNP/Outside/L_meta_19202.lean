import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19202

private def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.and, [2, 5]⟩, ⟨.not, [5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [0, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_19202

theorem PEqualNP.Outside.L_meta_19202 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4831 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19202.witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19202.witness]
  · unfold PEqualNP.Represents.Represents
    decide +kernel
