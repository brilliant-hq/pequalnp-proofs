import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24291
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [4]⟩,
        ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [1, 7]⟩,
        ⟨GateOp.and, [6, 9]⟩,
        ⟨GateOp.or, [0, 10]⟩,
        ⟨GateOp.and, [8, 11]⟩ ],
    output := 12 }

end PEqualNP.Outside.L_meta_24291

theorem PEqualNP.Outside.L_meta_24291 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33695 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24291.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_24291.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
