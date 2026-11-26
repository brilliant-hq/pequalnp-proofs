import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20177

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Pair row i with column p(i), for p = [1, 6, 5, 0, 2, 7, 3, 4].
-- Wires 16–23 test whether either endpoint is at the corresponding index.
-- Away from 3 and 7, an edge joins different classes among {0,5}, {2,1}, {6,4}.
-- Wire 34 joins 3 to {5,1,4,7}, and wire 37 joins 7 to {0,2,6}.
-- The loops at 3 and 7 are handled by wires 38 and 39.
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [1, 14]⟩,
    ⟨GateOp.or, [2, 13]⟩, ⟨GateOp.or, [3, 8]⟩,
    ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.or, [5, 15]⟩,
    ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.or, [7, 12]⟩,
    ⟨GateOp.or, [16, 21]⟩, ⟨GateOp.or, [18, 17]⟩,
    ⟨GateOp.or, [22, 20]⟩,
    ⟨GateOp.and, [24, 25]⟩, ⟨GateOp.or, [24, 25]⟩,
    ⟨GateOp.and, [28, 26]⟩, ⟨GateOp.or, [27, 29]⟩,
    ⟨GateOp.or, [21, 17]⟩, ⟨GateOp.or, [31, 20]⟩,
    ⟨GateOp.or, [32, 23]⟩, ⟨GateOp.and, [19, 33]⟩,
    ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.or, [35, 22]⟩,
    ⟨GateOp.and, [23, 36]⟩,
    ⟨GateOp.and, [3, 8]⟩, ⟨GateOp.and, [7, 12]⟩,
    ⟨GateOp.or, [30, 34]⟩, ⟨GateOp.or, [37, 38]⟩,
    ⟨GateOp.or, [40, 41]⟩, ⟨GateOp.or, [42, 39]⟩], 43⟩

theorem witness_mono : Monotone2 witness := by
  simp [Monotone2, witness]

end PEqualNP.Outside.L_meta_20177

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_20177 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4319635817910669180 : ℕ).testBit (8 * u.val + v.val)) 30 := by
  refine ⟨L_meta_20177.witness, L_meta_20177.witness_mono, by decide, ?_⟩
  decide
