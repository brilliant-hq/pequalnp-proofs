import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20279

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.or, [4, 12]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.or, [5, 14]⟩, ⟨GateOp.or, [6, 18]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.or, [21, 22]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [24, 15]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.or, [1, 20]⟩, ⟨GateOp.or, [11, 20]⟩, ⟨GateOp.or, [28, 21]⟩, ⟨GateOp.or, [7, 15]⟩, ⟨GateOp.or, [30, 19]⟩, ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.or, [1, 17]⟩, ⟨GateOp.or, [33, 19]⟩, ⟨GateOp.and, [13, 23]⟩, ⟨GateOp.and, [25, 26]⟩, ⟨GateOp.and, [22, 27]⟩, ⟨GateOp.and, [29, 31]⟩, ⟨GateOp.and, [32, 34]⟩, ⟨GateOp.or, [35, 36]⟩, ⟨GateOp.or, [40, 37]⟩, ⟨GateOp.or, [41, 38]⟩, ⟨GateOp.or, [42, 39]⟩], 43⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 100000 in
theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15612158718957067875 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_20279

theorem PEqualNP.Outside.L_meta_20279 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15612158718957067875 : ℕ).testBit (8 * u.val + v.val)) 28) :=
  PEqualNP.Outside.L_meta_20279.main_aux
