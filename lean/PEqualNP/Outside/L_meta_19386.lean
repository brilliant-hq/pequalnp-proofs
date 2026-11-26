import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.L_meta_19386_aux
open PEqualNP.CircuitLowerBounds
def circuit : Circuit := ⟨[
    ⟨.or, [1, 3]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [10, 14]⟩,
    ⟨.and, [11, 13]⟩,
    ⟨.and, [4, 15]⟩,
    ⟨.and, [12, 9]⟩,
    ⟨.or, [19, 18]⟩,
    ⟨.or, [20, 17]⟩,
    ⟨.or, [21, 16]⟩], 22⟩
end PEqualNP.Outside.L_meta_19386_aux

open PEqualNP.Outside.L_meta_19386_aux PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_19386 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3320506 : ℕ).testBit (5 * u.val + v.val)) 15 := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · decide +kernel
