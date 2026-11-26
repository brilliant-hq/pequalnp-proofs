import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22551

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def C : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [2, 3] },
      { op := GateOp.or, inputs := [0, 6] },
      { op := GateOp.or, inputs := [1, 3] },
      { op := GateOp.and, inputs := [2, 8] },
      { op := GateOp.or, inputs := [9, 1] },
      { op := GateOp.not, inputs := [6] },
      { op := GateOp.or, inputs := [11, 10] },
      { op := GateOp.and, inputs := [12, 7] }
    ], output := 13 }

private theorem C_fan : FanInTwo C := by
  intro g hg
  simp [C] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem C_size : C.size ≤ 8 := by
  decide

private theorem C_rep :
    ∀ i j : Fin 6,
      C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (33587 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide

end PEqualNP.Outside.L_meta_22551

theorem PEqualNP.Outside.L_meta_22551 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧
        ∀ i j : Fin 6,
          C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
            (33587 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22551.C,
   PEqualNP.Outside.L_meta_22551.C_fan,
   PEqualNP.Outside.L_meta_22551.C_size,
   PEqualNP.Outside.L_meta_22551.C_rep⟩
