import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19423_aux
open PEqualNP.CircuitLowerBounds
def circuit : Circuit := ⟨[
    ⟨.or, [9, 5]⟩,
    ⟨.not, [10]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.and, [13, 5]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [4, 3]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [16, 17]⟩,
    ⟨.or, [15, 18]⟩], 19⟩
end PEqualNP.Outside.L_meta_19423_aux

open PEqualNP.Outside.L_meta_19423_aux PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_19423 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24871982 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, circuit]
  · decide +kernel
