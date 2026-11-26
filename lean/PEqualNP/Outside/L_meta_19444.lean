import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19444_aux
open PEqualNP.CircuitLowerBounds
def circuit : Circuit := ⟨[
    ⟨.or, [5, 9]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.or, [5, 8]⟩,
    ⟨.or, [6, 12]⟩,
    ⟨.or, [0, 13]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.or, [15, 1]⟩,
    ⟨.not, [16]⟩,
    ⟨.and, [14, 17]⟩,
    ⟨.or, [11, 18]⟩], 19⟩
end PEqualNP.Outside.L_meta_19444_aux

open PEqualNP.Outside.L_meta_19444_aux PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_19444 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (11906614 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, circuit]
  · decide +kernel
