import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20675
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [6, 4]⟩,
        ⟨GateOp.or, [5, 2]⟩,
        ⟨GateOp.and, [7, 3]⟩,
        ⟨GateOp.or, [11, 8]⟩,
        ⟨GateOp.and, [1, 11]⟩,
        ⟨GateOp.and, [10, 13]⟩,
        ⟨GateOp.or, [12, 14]⟩,
        ⟨GateOp.or, [16, 15]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_20675

theorem PEqualNP.Outside.L_meta_20675 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (9570336 : ℕ).testBit (5 * u.val + v.val)) 8) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_20675.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20675.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
