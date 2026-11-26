import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19212

private def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.not, [5]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [9, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_19212

theorem PEqualNP.Outside.L_meta_19212 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (829 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19212.witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19212.witness]
  · unfold PEqualNP.Represents.Represents
    decide +kernel
