import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19426_aux
open PEqualNP.CircuitLowerBounds
def circuit : Circuit := ⟨[
    ⟨.and, [0, 7]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [9, 7]⟩,
    ⟨.not, [12]⟩,
    ⟨.and, [11, 13]⟩,
    ⟨.or, [10, 14]⟩,
    ⟨.or, [4, 3]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [16, 17]⟩,
    ⟨.or, [15, 18]⟩], 19⟩
end PEqualNP.Outside.L_meta_19426_aux

open PEqualNP.Outside.L_meta_19426_aux PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_19426 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24882532 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, circuit]
  · decide +kernel
