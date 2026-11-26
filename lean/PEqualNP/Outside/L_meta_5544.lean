import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5544 :
    PEqualNP.MetaComplexity.Monotone2 ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }], output := 8 } : PEqualNP.CircuitLowerBounds.Circuit) ∧
  ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }], output := 8 } : PEqualNP.CircuitLowerBounds.Circuit).size = 1 ∧
  PEqualNP.Represents.Represents (fun u v : Fin 4 => (255 : ℕ).testBit (4 * u.val + v.val)) ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }], output := 8 } : PEqualNP.CircuitLowerBounds.Circuit) := by
  refine ⟨?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
