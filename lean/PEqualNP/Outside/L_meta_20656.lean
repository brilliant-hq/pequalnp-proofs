import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20656 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (11770880 : ℕ).testBit (5 * u.val + v.val)) 7 := by
  exact ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }], output := 16 } : PEqualNP.CircuitLowerBounds.Circuit), by simp [PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩
