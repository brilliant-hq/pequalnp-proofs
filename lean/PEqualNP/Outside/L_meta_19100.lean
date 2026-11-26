import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19100

private def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.and, [2, 5]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [1, 4]⟩, ⟨.not, [10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [0, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_19100

theorem PEqualNP.Outside.L_meta_19100 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (5103 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19100.witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19100.witness]
  · unfold PEqualNP.Represents.Represents
    decide +kernel
