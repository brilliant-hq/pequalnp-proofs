import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19438_aux
open PEqualNP.CircuitLowerBounds
def circuit : Circuit := ⟨[
    ⟨.and, [0, 6]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.or, [1, 12]⟩,
    ⟨.or, [4, 9]⟩,
    ⟨.or, [10, 14]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.and, [13, 15]⟩,
    ⟨.not, [16]⟩,
    ⟨.or, [17, 18]⟩], 19⟩
end PEqualNP.Outside.L_meta_19438_aux

open PEqualNP.Outside.L_meta_19438_aux PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_19438 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3585970 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, circuit]
  · decide +kernel
