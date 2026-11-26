import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20686
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [8, 7]⟩,
        ⟨GateOp.or, [10, 5]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [11, 2]⟩,
        ⟨GateOp.or, [12, 6]⟩,
        ⟨GateOp.and, [1, 5]⟩,
        ⟨GateOp.and, [13, 14]⟩,
        ⟨GateOp.or, [16, 15]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_20686

theorem PEqualNP.Outside.L_meta_20686 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (14059552 : ℕ).testBit (5 * u.val + v.val)) 8) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_20686.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20686.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
