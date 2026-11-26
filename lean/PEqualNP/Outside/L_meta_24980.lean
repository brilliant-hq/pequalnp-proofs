import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24980
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.and, [3, 6]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.and, [7, 9]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.and, [2, 11]⟩,
        ⟨GateOp.or, [8, 12]⟩,
        ⟨GateOp.or, [10, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_24980

theorem PEqualNP.Outside.L_meta_24980 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6475580 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24980.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_24980.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
