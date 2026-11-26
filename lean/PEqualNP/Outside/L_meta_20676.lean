import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20676
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [7, 5]⟩,
        ⟨GateOp.or, [8, 5]⟩,
        ⟨GateOp.or, [5, 6]⟩,
        ⟨GateOp.and, [11, 4]⟩,
        ⟨GateOp.and, [2, 12]⟩,
        ⟨GateOp.and, [10, 3]⟩,
        ⟨GateOp.or, [15, 14]⟩,
        ⟨GateOp.or, [13, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_20676

theorem PEqualNP.Outside.L_meta_20676 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (9604096 : ℕ).testBit (5 * u.val + v.val)) 8) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_20676.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20676.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
