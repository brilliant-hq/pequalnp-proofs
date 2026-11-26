import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19838_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [9, 15]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [12, 18]⟩, ⟨GateOp.and, [0, 19]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.and, [1, 21]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [23, 14]⟩, ⟨GateOp.and, [2, 24]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [26, 14]⟩, ⟨GateOp.and, [3, 27]⟩, ⟨GateOp.or, [12, 16]⟩, ⟨GateOp.and, [4, 29]⟩, ⟨GateOp.or, [13, 17]⟩, ⟨GateOp.and, [5, 31]⟩, ⟨GateOp.or, [14, 18]⟩, ⟨GateOp.and, [6, 33]⟩, ⟨GateOp.or, [11, 17]⟩, ⟨GateOp.and, [7, 35]⟩, ⟨GateOp.or, [20, 22]⟩, ⟨GateOp.or, [37, 25]⟩, ⟨GateOp.or, [38, 28]⟩, ⟨GateOp.or, [39, 30]⟩, ⟨GateOp.or, [40, 32]⟩, ⟨GateOp.or, [41, 34]⟩, ⟨GateOp.or, [42, 36]⟩], 43⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_19838_aux

theorem PEqualNP.Outside.L_meta_19838 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9972273704342751540 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_meta_19838_aux.wit, PEqualNP.Outside.L_meta_19838_aux.wit_mono, by decide, by decide +kernel⟩
