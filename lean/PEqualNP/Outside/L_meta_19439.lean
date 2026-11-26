import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19439_aux
open PEqualNP.CircuitLowerBounds
def circuit : Circuit := ⟨[
    ⟨.and, [1, 5]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [11, 4]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [0, 14]⟩,
    ⟨.or, [5, 4]⟩,
    ⟨.not, [16]⟩,
    ⟨.and, [15, 17]⟩,
    ⟨.or, [13, 18]⟩], 19⟩
end PEqualNP.Outside.L_meta_19439_aux

open PEqualNP.Outside.L_meta_19439_aux PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_19439 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3957566 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, circuit]
  · decide +kernel
