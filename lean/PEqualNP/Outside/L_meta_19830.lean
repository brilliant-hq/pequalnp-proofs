import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19830_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [9, 13]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [8, 14]⟩, ⟨GateOp.or, [8, 15]⟩, ⟨GateOp.or, [10, 15]⟩, ⟨GateOp.or, [14, 17]⟩, ⟨GateOp.or, [17, 19]⟩, ⟨GateOp.and, [0, 22]⟩, ⟨GateOp.or, [16, 19]⟩, ⟨GateOp.and, [1, 24]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [26, 20]⟩, ⟨GateOp.and, [2, 27]⟩, ⟨GateOp.or, [16, 20]⟩, ⟨GateOp.and, [3, 29]⟩, ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.and, [4, 31]⟩, ⟨GateOp.or, [10, 21]⟩, ⟨GateOp.and, [5, 33]⟩, ⟨GateOp.or, [13, 21]⟩, ⟨GateOp.and, [6, 35]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [37, 18]⟩, ⟨GateOp.and, [7, 38]⟩, ⟨GateOp.or, [23, 25]⟩, ⟨GateOp.or, [40, 28]⟩, ⟨GateOp.or, [41, 30]⟩, ⟨GateOp.or, [42, 32]⟩, ⟨GateOp.or, [43, 34]⟩, ⟨GateOp.or, [44, 36]⟩, ⟨GateOp.or, [45, 39]⟩], 46⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_19830_aux

theorem PEqualNP.Outside.L_meta_19830 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5582313321192137625 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨PEqualNP.Outside.L_meta_19830_aux.wit, PEqualNP.Outside.L_meta_19830_aux.wit_mono, by decide, by decide +kernel⟩
