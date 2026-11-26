import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19435_aux
open PEqualNP.CircuitLowerBounds
def circuit : Circuit := ⟨[
    ⟨.and, [2, 5]⟩,
    ⟨.or, [6, 10]⟩,
    ⟨.or, [0, 11]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [1, 13]⟩,
    ⟨.or, [7, 12]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.and, [14, 15]⟩,
    ⟨.not, [17]⟩,
    ⟨.and, [16, 18]⟩], 19⟩
end PEqualNP.Outside.L_meta_19435_aux

open PEqualNP.Outside.L_meta_19435_aux PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_19435 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3269438 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, circuit]
  · decide +kernel
