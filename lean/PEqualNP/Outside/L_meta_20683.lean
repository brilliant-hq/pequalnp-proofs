import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20683 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (13698080 : ℕ).testBit (5 * u.val + v.val)) 8) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 16] }], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
