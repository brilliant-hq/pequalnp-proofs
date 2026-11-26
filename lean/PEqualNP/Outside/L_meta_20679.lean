import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20679
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 7]⟩,
        ⟨GateOp.or, [6, 10]⟩,
        ⟨GateOp.or, [8, 6]⟩,
        ⟨GateOp.or, [5, 3]⟩,
        ⟨GateOp.or, [12, 13]⟩,
        ⟨GateOp.and, [14, 4]⟩,
        ⟨GateOp.and, [11, 13]⟩,
        ⟨GateOp.or, [15, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_20679

theorem PEqualNP.Outside.L_meta_20679 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (11731968 : ℕ).testBit (5 * u.val + v.val)) 8) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_20679.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20679.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
