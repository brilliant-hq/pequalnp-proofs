import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19430_aux
open PEqualNP.CircuitLowerBounds
def circuit : Circuit := ⟨[
    ⟨.and, [4, 8]⟩,
    ⟨.or, [5, 8]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [0, 13]⟩,
    ⟨.or, [3, 12]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.and, [14, 15]⟩,
    ⟨.not, [17]⟩,
    ⟨.and, [16, 18]⟩], 19⟩
end PEqualNP.Outside.L_meta_19430_aux

open PEqualNP.Outside.L_meta_19430_aux PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_19430 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7661366 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, circuit]
  · decide +kernel
