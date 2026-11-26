import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19427_aux
open PEqualNP.CircuitLowerBounds
def circuit : Circuit := ⟨[
    ⟨.or, [7, 8]⟩,
    ⟨.or, [10, 6]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.and, [1, 5]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [4, 2]⟩,
    ⟨.or, [3, 15]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [16, 17]⟩,
    ⟨.or, [14, 18]⟩], 19⟩
end PEqualNP.Outside.L_meta_19427_aux

open PEqualNP.Outside.L_meta_19427_aux PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_19427 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24894510 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, circuit]
  · decide +kernel
