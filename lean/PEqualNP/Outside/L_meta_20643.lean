import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20643 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7373824 : ℕ).testBit (5 * u.val + v.val)) 6) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
