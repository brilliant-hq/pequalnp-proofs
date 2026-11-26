import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20349

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [4, 14]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [3, 16]⟩, ⟨GateOp.or, [1, 13]⟩, ⟨GateOp.or, [22, 15]⟩, ⟨GateOp.or, [10, 17]⟩, ⟨GateOp.or, [3, 20]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.or, [26, 15]⟩, ⟨GateOp.or, [27, 19]⟩, ⟨GateOp.or, [17, 18]⟩, ⟨GateOp.or, [1, 16]⟩, ⟨GateOp.or, [30, 19]⟩, ⟨GateOp.or, [2, 13]⟩, ⟨GateOp.or, [32, 18]⟩, ⟨GateOp.or, [33, 20]⟩, ⟨GateOp.and, [21, 23]⟩, ⟨GateOp.and, [24, 25]⟩, ⟨GateOp.and, [28, 29]⟩, ⟨GateOp.and, [31, 34]⟩, ⟨GateOp.or, [35, 36]⟩, ⟨GateOp.or, [39, 37]⟩, ⟨GateOp.or, [40, 38]⟩], 41⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 100000 in
theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5580678593250014130 : ℕ).testBit (8 * u.val + v.val)) 26 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_20349

theorem PEqualNP.Outside.L_meta_20349 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5580678593250014130 : ℕ).testBit (8 * u.val + v.val)) 26) :=
  PEqualNP.Outside.L_meta_20349.main_aux
