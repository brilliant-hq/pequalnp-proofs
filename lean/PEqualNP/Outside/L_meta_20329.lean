import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20329

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [4, 14]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.or, [5, 15]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.or, [18, 20]⟩, ⟨GateOp.or, [0, 13]⟩, ⟨GateOp.or, [22, 16]⟩, ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.or, [24, 19]⟩, ⟨GateOp.or, [15, 21]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [13, 17]⟩, ⟨GateOp.or, [28, 19]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [30, 10]⟩, ⟨GateOp.or, [31, 11]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.or, [33, 21]⟩, ⟨GateOp.or, [1, 12]⟩, ⟨GateOp.and, [23, 25]⟩, ⟨GateOp.and, [26, 27]⟩, ⟨GateOp.and, [29, 32]⟩, ⟨GateOp.and, [34, 35]⟩, ⟨GateOp.or, [36, 37]⟩, ⟨GateOp.or, [40, 38]⟩, ⟨GateOp.or, [41, 39]⟩], 42⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 100000 in
theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14203909686430943145 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_20329

theorem PEqualNP.Outside.L_meta_20329 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14203909686430943145 : ℕ).testBit (8 * u.val + v.val)) 27) :=
  PEqualNP.Outside.L_meta_20329.main_aux
