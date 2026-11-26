import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23242

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates :=
      [ { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [4] }
      , { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }
      , { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 7] }
      , { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }
      , { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 9] }
      , { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }
      ]
    output := 11 }

end PEqualNP.Outside.L_meta_23242

theorem PEqualNP.Outside.L_meta_23242 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101295 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_23242.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_23242.witness]
