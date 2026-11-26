import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23030

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def C : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [0, 1] },
      { op := GateOp.or, inputs := [2, 5] },
      { op := GateOp.or, inputs := [7, 2] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.and, inputs := [6, 9] },
      { op := GateOp.or, inputs := [2, 0] },
      { op := GateOp.and, inputs := [11, 3] },
      { op := GateOp.or, inputs := [12, 10] }
    ], output := 13 }

private theorem C_mono : Monotone2 C := by
  intro g hg
  simp [C] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem C_size : C.size ≤ 8 := by
  decide

private theorem C_rep :
    ∀ i j : Fin 6,
      C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (36156 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide

end PEqualNP.Outside.L_meta_23030

theorem PEqualNP.Outside.L_meta_23030 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧
        ∀ i j : Fin 6,
          C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
            (36156 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_23030.C,
   PEqualNP.Outside.L_meta_23030.C_mono,
   PEqualNP.Outside.L_meta_23030.C_size,
   PEqualNP.Outside.L_meta_23030.C_rep⟩
