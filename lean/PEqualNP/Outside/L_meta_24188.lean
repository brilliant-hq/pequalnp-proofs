import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24188

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C0 : Circuit :=
  ⟨[⟨GateOp.and, [0, 2]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.or, [0, 3]⟩,
    ⟨GateOp.and, [6, 7]⟩,
    ⟨GateOp.or, [1, 8]⟩,
    ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.or, [2, 10]⟩,
    ⟨GateOp.or, [8, 11]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [9, 13]⟩,
    ⟨GateOp.not, [14]⟩,
    ⟨GateOp.and, [12, 15]⟩], 16⟩

theorem ok0 : FanInTwo C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_24188

theorem PEqualNP.Outside.L_meta_24188 :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧
      ∀ i j : Fin 5,
        C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
          (283226 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24188.C0, PEqualNP.Outside.L_meta_24188.ok0,
    by decide, by decide +kernel⟩
