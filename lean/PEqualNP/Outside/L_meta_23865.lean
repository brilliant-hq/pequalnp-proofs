import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23865

open PEqualNP.CircuitLowerBounds

def upperC : Circuit :=
  { gates :=
      [ { op := GateOp.or, inputs := [3, 4] },
        { op := GateOp.or, inputs := [1, 2] },
        { op := GateOp.or, inputs := [0, 6] },
        { op := GateOp.or, inputs := [1, 5] },
        { op := GateOp.and, inputs := [2, 8] },
        { op := GateOp.not, inputs := [9] },
        { op := GateOp.and, inputs := [7, 10] } ],
    output := 11 }

theorem upper_fanInTwo : PEqualNP.MetaComplexity.FanInTwo upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_eval : ∀ i j : Fin 5,
    upperC.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
      (4959 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_23865

theorem PEqualNP.Outside.L_meta_23865 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4959 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_23865.upperC, PEqualNP.Outside.L_meta_23865.upper_fanInTwo, by decide,
    PEqualNP.Outside.L_meta_23865.upper_eval⟩
