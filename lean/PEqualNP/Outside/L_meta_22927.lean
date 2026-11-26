import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22927

def C : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates :=
      [ { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] },
        { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] },
        { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 6] },
        { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] },
        { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 6] },
        { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 5] },
        { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] },
        { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 10] } ],
    output := 12 }

theorem mono : PEqualNP.MetaComplexity.Monotone2 C := by
  simp [C, PEqualNP.MetaComplexity.Monotone2]

theorem rep : ∀ i j : Fin 5,
    C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
      (25502 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_22927

theorem PEqualNP.Outside.L_meta_22927 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (25502 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_22927.C, PEqualNP.Outside.L_meta_22927.mono, by decide,
    PEqualNP.Outside.L_meta_22927.rep⟩
