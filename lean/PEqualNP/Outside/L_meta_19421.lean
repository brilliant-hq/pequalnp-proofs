import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19421_aux
open PEqualNP.CircuitLowerBounds
def circuit : Circuit := ⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [7, 6]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [4, 14]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.or, [3, 2]⟩,
    ⟨.and, [17, 5]⟩,
    ⟨.or, [16, 18]⟩], 19⟩
end PEqualNP.Outside.L_meta_19421_aux

open PEqualNP.Outside.L_meta_19421_aux PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_19421 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24151502 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, circuit]
  · decide +kernel
