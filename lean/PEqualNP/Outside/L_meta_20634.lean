import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.RepReads

namespace PEqualNP.Outside.L_meta_20634

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [10, 3]⟩,
    ⟨.and, [11, 5]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [13, 8]⟩,
    ⟨.or, [14, 9]⟩,
    ⟨.and, [4, 15]⟩,
    ⟨.or, [12, 16]⟩
  ], 17⟩

theorem upper :
    RepSizeAtMost (fun u v : Fin 5 => (31491104 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  refine ⟨witness, ?_, by decide +kernel, by decide +kernel⟩
  simp [Monotone2, witness]

end PEqualNP.Outside.L_meta_20634

theorem PEqualNP.Outside.L_meta_20634 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31491104 : ℕ).testBit (5 * u.val + v.val)) 8 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31491104 : ℕ).testBit (5 * u.val + v.val)) 7) := by
  refine ⟨PEqualNP.Outside.L_meta_20634.upper, ?_⟩
  intro h
  let A : Fin 5 → Fin 5 → Bool := fun u v => (31491104 : ℕ).testBit (5 * u.val + v.val)
  have hcount :
      (PEqualNP.MetaComplexity.RepReads.forcedL A).card +
        (PEqualNP.MetaComplexity.RepReads.forcedR A).card = 9 := by
    decide +kernel
  have hb := PEqualNP.MetaComplexity.RepReads.reads_le A h
  omega
