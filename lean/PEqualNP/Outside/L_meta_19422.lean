import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19422_aux
open PEqualNP.CircuitLowerBounds
def circuit : Circuit := ⟨[
    ⟨.and, [0, 7]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.not, [11]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.or, [13, 5]⟩,
    ⟨.and, [12, 14]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [4, 17]⟩,
    ⟨.or, [16, 18]⟩], 19⟩
end PEqualNP.Outside.L_meta_19422_aux

open PEqualNP.Outside.L_meta_19422_aux PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_19422 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24489316 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, circuit]
  · decide +kernel
