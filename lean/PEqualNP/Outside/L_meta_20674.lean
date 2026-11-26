import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20674
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 6]⟩,
        ⟨GateOp.or, [2, 7]⟩,
        ⟨GateOp.or, [11, 6]⟩,
        ⟨GateOp.and, [11, 10]⟩,
        ⟨GateOp.or, [13, 4]⟩,
        ⟨GateOp.or, [3, 12]⟩,
        ⟨GateOp.or, [14, 5]⟩,
        ⟨GateOp.and, [15, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_20674

theorem PEqualNP.Outside.L_meta_20674 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (6458368 : ℕ).testBit (5 * u.val + v.val)) 8) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_20674.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20674.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
