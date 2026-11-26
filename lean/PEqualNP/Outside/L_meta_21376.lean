import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21376 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103899 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }], output := 20 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
