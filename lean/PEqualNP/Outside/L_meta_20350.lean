import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20350

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 10]⟩,
    ⟨GateOp.or, [1, 13]⟩,
    ⟨GateOp.or, [2, 12]⟩,
    ⟨GateOp.or, [3, 15]⟩,
    ⟨GateOp.or, [4, 8]⟩,
    ⟨GateOp.or, [5, 14]⟩,
    ⟨GateOp.or, [6, 11]⟩,
    ⟨GateOp.or, [7, 9]⟩,
    ⟨GateOp.or, [18, 19]⟩,
    ⟨GateOp.or, [20, 22]⟩,
    ⟨GateOp.and, [24, 25]⟩,
    ⟨GateOp.or, [19, 20]⟩,
    ⟨GateOp.or, [27, 23]⟩,
    ⟨GateOp.and, [16, 28]⟩,
    ⟨GateOp.or, [21, 12]⟩,
    ⟨GateOp.or, [17, 22]⟩,
    ⟨GateOp.and, [30, 31]⟩,
    ⟨GateOp.or, [21, 2]⟩,
    ⟨GateOp.or, [33, 13]⟩,
    ⟨GateOp.or, [23, 1]⟩,
    ⟨GateOp.and, [34, 35]⟩,
    ⟨GateOp.or, [26, 29]⟩,
    ⟨GateOp.or, [37, 32]⟩,
    ⟨GateOp.or, [38, 36]⟩], 39⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7264353014310989955 : ℕ).testBit (8 * u.val + v.val)) 25 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_20350

theorem PEqualNP.Outside.L_meta_20350 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7264353014310989955 : ℕ).testBit (8 * u.val + v.val)) 25 :=
  PEqualNP.Outside.L_meta_20350.main_aux
