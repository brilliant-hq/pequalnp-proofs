import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19093

private def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [0, 7]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [3, 11]⟩, ⟨.not, [12]⟩], 13⟩

end PEqualNP.Outside.L_meta_19093

theorem PEqualNP.Outside.L_meta_19093 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (1915 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19093.witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19093.witness]
  · unfold PEqualNP.Represents.Represents
    decide +kernel
