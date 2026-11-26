import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19425_aux
open PEqualNP.CircuitLowerBounds
def circuit : Circuit := ⟨[
    ⟨.or, [4, 3]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [10, 11]⟩,
    ⟨.or, [2, 1]⟩,
    ⟨.or, [8, 5]⟩,
    ⟨.and, [13, 14]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [7, 6]⟩,
    ⟨.and, [0, 17]⟩,
    ⟨.or, [16, 18]⟩], 19⟩
end PEqualNP.Outside.L_meta_19425_aux

open PEqualNP.Outside.L_meta_19425_aux PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_19425 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24880422 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, circuit]
  · decide +kernel
