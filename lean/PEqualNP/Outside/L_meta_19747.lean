import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19747_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [8, 9]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [11, 20]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [8, 21]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [13, 20]⟩, ⟨.and, [2, 26]⟩, ⟨.or, [15, 21]⟩, ⟨.and, [3, 28]⟩, ⟨.or, [9, 21]⟩, ⟨.and, [4, 30]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [32, 19]⟩, ⟨.and, [5, 33]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [35, 18]⟩, ⟨.and, [6, 36]⟩, ⟨.or, [14, 20]⟩, ⟨.and, [7, 38]⟩, ⟨.or, [23, 25]⟩, ⟨.or, [40, 27]⟩, ⟨.or, [41, 29]⟩, ⟨.or, [42, 31]⟩, ⟨.or, [43, 34]⟩, ⟨.or, [44, 37]⟩, ⟨.or, [45, 39]⟩], 46⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g => (g.op matches GateOp.and || g.op matches GateOp.or) && decide (g.inputs.length ≤ 2)

theorem okB_mono (C : Circuit) (h : okB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp_all

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14348455746820602255 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨circ, okB_mono circ (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19747_aux

theorem PEqualNP.Outside.L_meta_19747 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14348455746820602255 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_19747_aux.main
