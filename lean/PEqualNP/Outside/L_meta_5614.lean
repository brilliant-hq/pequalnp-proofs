import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5614 :
    PEqualNP.MetaComplexity.Monotone2 ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 8] }], output := 9 } : PEqualNP.CircuitLowerBounds.Circuit) ∧
  ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 8] }], output := 9 } : PEqualNP.CircuitLowerBounds.Circuit).size = 2 ∧
  PEqualNP.Represents.Represents (fun u v : Fin 4 => (4095 : ℕ).testBit (4 * u.val + v.val)) ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 8] }], output := 9 } : PEqualNP.CircuitLowerBounds.Circuit) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
