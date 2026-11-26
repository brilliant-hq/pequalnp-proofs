import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19096

private def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [3, 12]⟩, ⟨.not, [13]⟩], 14⟩

end PEqualNP.Outside.L_meta_19096

theorem PEqualNP.Outside.L_meta_19096 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (1981 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19096.witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19096.witness]
  · unfold PEqualNP.Represents.Represents
    decide +kernel
