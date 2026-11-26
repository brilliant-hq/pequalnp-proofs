import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20138

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  { gates := [
    { op := GateOp.or, inputs := [2, 4] },
    { op := GateOp.or, inputs := [16, 5] },
    { op := GateOp.or, inputs := [10, 11] },
    { op := GateOp.or, inputs := [18, 12] },
    { op := GateOp.and, inputs := [17, 19] },
    { op := GateOp.or, inputs := [3, 7] },
    { op := GateOp.or, inputs := [9, 11] },
    { op := GateOp.or, inputs := [22, 14] },
    { op := GateOp.or, inputs := [23, 15] },
    { op := GateOp.and, inputs := [21, 24] },
    { op := GateOp.or, inputs := [0, 2] },
    { op := GateOp.or, inputs := [26, 6] },
    { op := GateOp.or, inputs := [8, 13] },
    { op := GateOp.and, inputs := [27, 28] },
    { op := GateOp.or, inputs := [1, 6] },
    { op := GateOp.or, inputs := [9, 10] },
    { op := GateOp.or, inputs := [31, 14] },
    { op := GateOp.and, inputs := [30, 32] },
    { op := GateOp.or, inputs := [0, 1] },
    { op := GateOp.or, inputs := [34, 4] },
    { op := GateOp.or, inputs := [13, 15] },
    { op := GateOp.and, inputs := [35, 36] },
    { op := GateOp.or, inputs := [0, 7] },
    { op := GateOp.or, inputs := [9, 12] },
    { op := GateOp.and, inputs := [38, 39] },
    { op := GateOp.or, inputs := [3, 5] },
    { op := GateOp.or, inputs := [8, 14] },
    { op := GateOp.and, inputs := [41, 42] },
    { op := GateOp.or, inputs := [20, 25] },
    { op := GateOp.or, inputs := [44, 29] },
    { op := GateOp.or, inputs := [45, 33] },
    { op := GateOp.or, inputs := [46, 37] },
    { op := GateOp.or, inputs := [47, 40] },
    { op := GateOp.or, inputs := [48, 43] }],
    output := 49 }

theorem mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_20138

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_20138 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15737650488314554035 : ℕ).testBit (8 * u.val + v.val)) 34) :=
  ⟨PEqualNP.Outside.L_meta_20138.circ, PEqualNP.Outside.L_meta_20138.mono, by decide, by decide⟩
