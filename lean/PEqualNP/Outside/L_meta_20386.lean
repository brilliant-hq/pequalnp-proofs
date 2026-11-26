import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20386

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [0, 15]⟩, ⟨GateOp.or, [16, 17]⟩,
    ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.or, [6, 19]⟩, ⟨GateOp.and, [18, 20]⟩,
    ⟨GateOp.or, [14, 19]⟩, ⟨GateOp.or, [16, 22]⟩, ⟨GateOp.or, [5, 10]⟩,
    ⟨GateOp.or, [4, 13]⟩, ⟨GateOp.or, [24, 25]⟩, ⟨GateOp.and, [23, 26]⟩,
    ⟨GateOp.or, [21, 27]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [14, 25]⟩,
    ⟨GateOp.or, [29, 30]⟩, ⟨GateOp.or, [3, 12]⟩, ⟨GateOp.or, [1, 32]⟩,
    ⟨GateOp.and, [31, 33]⟩, ⟨GateOp.or, [28, 34]⟩, ⟨GateOp.or, [8, 24]⟩,
    ⟨GateOp.or, [6, 17]⟩, ⟨GateOp.and, [36, 37]⟩, ⟨GateOp.or, [35, 38]⟩,
    ⟨GateOp.or, [1, 17]⟩, ⟨GateOp.and, [32, 40]⟩, ⟨GateOp.or, [39, 41]⟩], 42⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4361677255813263645 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_20386

theorem PEqualNP.Outside.L_meta_20386 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4361677255813263645 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20386.main_aux
