import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19545

private def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [1, 4]⟩, ⟨.and, [1, 4]⟩, ⟨.not, [9]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [0, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_19545

theorem PEqualNP.Outside.L_meta_19545 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4591 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19545.witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19545.witness]
  · unfold PEqualNP.Represents.Represents
    decide +kernel
