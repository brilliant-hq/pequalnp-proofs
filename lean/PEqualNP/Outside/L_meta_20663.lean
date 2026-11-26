import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20663 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15830016 : ℕ).testBit (5 * u.val + v.val)) 7) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 15] }], output := 16 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
