import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19428_aux
open PEqualNP.CircuitLowerBounds
def circuit : Circuit := ⟨[
    ⟨.or, [5, 8]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.not, [15]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [16, 17]⟩,
    ⟨.or, [14, 18]⟩], 19⟩
end PEqualNP.Outside.L_meta_19428_aux

open PEqualNP.Outside.L_meta_19428_aux PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_19428 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24894758 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, circuit]
  · decide +kernel
