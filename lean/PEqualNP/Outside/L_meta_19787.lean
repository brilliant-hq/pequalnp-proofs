import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19787_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [8, 11]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [22, 18]⟩, ⟨.and, [0, 23]⟩, ⟨.or, [13, 20]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [8, 20]⟩, ⟨.and, [2, 27]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [29, 19]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [9, 21]⟩, ⟨.and, [4, 32]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [34, 15]⟩, ⟨.or, [35, 16]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [14, 21]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [10, 20]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [24, 26]⟩, ⟨.or, [42, 28]⟩, ⟨.or, [43, 31]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [45, 37]⟩, ⟨.or, [46, 39]⟩, ⟨.or, [47, 41]⟩], 48⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g => (g.op matches GateOp.and || g.op matches GateOp.or) && decide (g.inputs.length ≤ 2)

theorem okB_mono (C : Circuit) (h : okB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp_all

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15451209511025767005 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨circ, okB_mono circ (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19787_aux

theorem PEqualNP.Outside.L_meta_19787 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15451209511025767005 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_19787_aux.main
