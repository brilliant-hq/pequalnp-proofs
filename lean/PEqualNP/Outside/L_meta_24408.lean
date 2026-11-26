import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24408_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [4, 5] }, { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [3, 6] }, { op := GateOp.not, inputs := [6] },
      { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.and, inputs := [7, 9] },
      { op := GateOp.or, inputs := [10, 11] }],
    output := 12 }

theorem upper_fan : FanInTwo upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_ok : ∀ i j : Fin 6, upperC.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (50110 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24408_aux

theorem PEqualNP.Outside.L_meta_24408 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50110 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24408_aux.upperC, PEqualNP.Outside.L_meta_24408_aux.upper_fan, by decide, PEqualNP.Outside.L_meta_24408_aux.upper_ok⟩
