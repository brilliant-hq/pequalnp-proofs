import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.L_meta_19364_aux
open PEqualNP.CircuitLowerBounds
def circuit : Circuit := ⟨[
    ⟨.or, [1, 5]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [0, 11]⟩,
    ⟨.or, [5, 12]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.not, [14]⟩,
    ⟨.and, [13, 15]⟩], 16⟩
end PEqualNP.Outside.L_meta_19364_aux

open PEqualNP.Outside.L_meta_19364_aux PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_19364 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7576638 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, circuit]
  · decide +kernel
