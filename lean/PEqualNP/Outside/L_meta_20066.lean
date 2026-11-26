import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20066

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 10]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [19, 17]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [21, 12]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [23, 18]⟩, ⟨GateOp.or, [4, 13]⟩, ⟨GateOp.or, [25, 16]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.or, [27, 16]⟩, ⟨GateOp.or, [3, 15]⟩, ⟨GateOp.or, [29, 18]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [31, 14]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.or, [33, 17]⟩, ⟨GateOp.and, [20, 22]⟩, ⟨GateOp.and, [24, 26]⟩, ⟨GateOp.and, [28, 30]⟩, ⟨GateOp.and, [32, 34]⟩, ⟨GateOp.or, [35, 36]⟩, ⟨GateOp.or, [39, 37]⟩, ⟨GateOp.or, [40, 38]⟩], 41⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 100000 in
theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9972273704342751540 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_20066

theorem PEqualNP.Outside.L_meta_20066 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9972273704342751540 : ℕ).testBit (8 * u.val + v.val)) 27) :=
  PEqualNP.Outside.L_meta_20066.main_aux
