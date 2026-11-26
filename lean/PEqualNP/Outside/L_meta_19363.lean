import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.L_meta_19363_aux
open PEqualNP.CircuitLowerBounds
def circuit : Circuit := ⟨[
    ⟨.or, [1, 5]⟩,
    ⟨.or, [6, 10]⟩,
    ⟨.or, [0, 11]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [0, 13]⟩,
    ⟨.and, [10, 14]⟩,
    ⟨.not, [15]⟩,
    ⟨.and, [12, 16]⟩], 17⟩
end PEqualNP.Outside.L_meta_19363_aux

open PEqualNP.Outside.L_meta_19363_aux PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_19363 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3247934 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, circuit]
  · decide +kernel
