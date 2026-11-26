import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19650 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7586195 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 18] }], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel

