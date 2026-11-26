import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19436_aux
open PEqualNP.CircuitLowerBounds
def circuit : Circuit := ⟨[
    ⟨.or, [2, 4]⟩,
    ⟨.and, [6, 10]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.not, [12]⟩,
    ⟨.and, [3, 7]⟩,
    ⟨.or, [14, 5]⟩,
    ⟨.or, [1, 15]⟩,
    ⟨.or, [0, 16]⟩,
    ⟨.and, [13, 17]⟩,
    ⟨.or, [11, 18]⟩], 19⟩
end PEqualNP.Outside.L_meta_19436_aux

open PEqualNP.Outside.L_meta_19436_aux PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_19436 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3312573 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, circuit]
  · decide +kernel
