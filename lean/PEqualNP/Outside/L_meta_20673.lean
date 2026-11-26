import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20673
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [5, 8]⟩,
        ⟨GateOp.or, [7, 9]⟩,
        ⟨GateOp.or, [5, 6]⟩,
        ⟨GateOp.or, [10, 11]⟩,
        ⟨GateOp.and, [3, 12]⟩,
        ⟨GateOp.and, [4, 13]⟩,
        ⟨GateOp.or, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_20673

theorem PEqualNP.Outside.L_meta_20673 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (30507008 : ℕ).testBit (5 * u.val + v.val)) 7) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_20673.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20673.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
