import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19434_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.and, [9, 10]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.or, [6, 12]⟩,
    ⟨.or, [0, 14]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.and, [13, 15]⟩,
    ⟨.not, [17]⟩,
    ⟨.and, [16, 18]⟩], 19⟩

end PEqualNP.Outside.L_meta_19434_aux

theorem PEqualNP.Outside.L_meta_19434 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3258290 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19434_aux.witness, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19434_aux.witness]
  · decide
  · decide +kernel
