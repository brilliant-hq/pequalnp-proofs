import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20638 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (5341184 : ℕ).testBit (5 * u.val + v.val)) 5) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
