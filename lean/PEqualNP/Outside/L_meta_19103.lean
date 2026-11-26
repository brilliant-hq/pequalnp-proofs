import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19103

private def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [8, 9]⟩, ⟨.not, [11]⟩, ⟨.and, [10, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_19103

theorem PEqualNP.Outside.L_meta_19103 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (13278 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19103.witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19103.witness]
  · unfold PEqualNP.Represents.Represents
    decide +kernel
