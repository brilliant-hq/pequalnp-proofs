import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19770

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def witness : Circuit :=
  ⟨[⟨GateOp.or, [8, 15]⟩, ⟨GateOp.or, [10, 13]⟩,
    ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [11, 17]⟩,
    ⟨GateOp.or, [12, 16]⟩, ⟨GateOp.or, [11, 20]⟩,
    ⟨GateOp.and, [0, 21]⟩, ⟨GateOp.or, [9, 14]⟩,
    ⟨GateOp.or, [23, 17]⟩, ⟨GateOp.and, [1, 24]⟩,
    ⟨GateOp.or, [8, 19]⟩, ⟨GateOp.and, [2, 26]⟩,
    ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [28, 16]⟩,
    ⟨GateOp.and, [3, 29]⟩, ⟨GateOp.or, [13, 14]⟩,
    ⟨GateOp.or, [31, 18]⟩, ⟨GateOp.and, [4, 32]⟩,
    ⟨GateOp.or, [14, 19]⟩, ⟨GateOp.and, [5, 34]⟩,
    ⟨GateOp.or, [11, 15]⟩, ⟨GateOp.or, [36, 18]⟩,
    ⟨GateOp.and, [6, 37]⟩, ⟨GateOp.or, [14, 20]⟩,
    ⟨GateOp.and, [7, 39]⟩, ⟨GateOp.or, [22, 25]⟩,
    ⟨GateOp.or, [41, 27]⟩, ⟨GateOp.or, [42, 30]⟩,
    ⟨GateOp.or, [43, 33]⟩, ⟨GateOp.or, [44, 35]⟩,
    ⟨GateOp.or, [45, 38]⟩, ⟨GateOp.or, [46, 40]⟩], 47⟩

private theorem witness_mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> simp

end PEqualNP.Outside.L_meta_19770

open PEqualNP.Outside.L_meta_19770

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_19770 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15103503539490350745 : ℕ).testBit (8 * u.val + v.val)) 32 := by
  refine ⟨witness, witness_mono, by decide, ?_⟩
  decide
