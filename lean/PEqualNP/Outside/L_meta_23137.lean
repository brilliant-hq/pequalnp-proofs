import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23137
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [2, 13]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.and, [1, 15]⟩,
        ⟨GateOp.and, [9, 14]⟩, ⟨GateOp.or, [16, 17]⟩ ],
    output := 18 }

end PEqualNP.Outside.L_meta_23137

theorem PEqualNP.Outside.L_meta_23137 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (5110 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  refine ⟨PEqualNP.Outside.L_meta_23137.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_23137.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
