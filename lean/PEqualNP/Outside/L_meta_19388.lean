import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.L_meta_19388_aux
open PEqualNP.CircuitLowerBounds
def circuit : Circuit := ⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [3, 10]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.and, [11, 13]⟩,
    ⟨.and, [0, 15]⟩,
    ⟨.and, [12, 9]⟩,
    ⟨.and, [4, 14]⟩,
    ⟨.or, [19, 18]⟩,
    ⟨.or, [20, 17]⟩,
    ⟨.or, [21, 16]⟩], 22⟩
end PEqualNP.Outside.L_meta_19388_aux

open PEqualNP.Outside.L_meta_19388_aux PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_19388 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3675834 : ℕ).testBit (5 * u.val + v.val)) 14 := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · decide +kernel
