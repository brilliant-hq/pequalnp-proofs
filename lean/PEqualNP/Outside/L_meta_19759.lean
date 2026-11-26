import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19759_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [8, 15]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [11, 19]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [24, 18]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [27, 15]⟩, ⟨.or, [28, 18]⟩, ⟨.and, [2, 29]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [3, 31]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [33, 19]⟩, ⟨.and, [4, 34]⟩, ⟨.or, [17, 21]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [38, 13]⟩, ⟨.or, [39, 17]⟩, ⟨.and, [6, 40]⟩, ⟨.or, [16, 21]⟩, ⟨.and, [7, 42]⟩, ⟨.or, [23, 26]⟩, ⟨.or, [44, 30]⟩, ⟨.or, [45, 32]⟩, ⟨.or, [46, 35]⟩, ⟨.or, [47, 37]⟩, ⟨.or, [48, 41]⟩, ⟨.or, [49, 43]⟩], 50⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g => (g.op matches GateOp.and || g.op matches GateOp.or) && decide (g.inputs.length ≤ 2)

theorem okB_mono (C : Circuit) (h : okB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp_all

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12498470449173941205 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  ⟨circ, okB_mono circ (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19759_aux

theorem PEqualNP.Outside.L_meta_19759 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12498470449173941205 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  PEqualNP.Outside.L_meta_19759_aux.main
