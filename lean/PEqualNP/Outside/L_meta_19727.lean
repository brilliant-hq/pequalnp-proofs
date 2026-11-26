import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19727_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [10, 13]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [21, 16]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [24, 19]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [27, 20]⟩, ⟨.and, [2, 28]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [32, 18]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [16, 17]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [6, 37]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [39, 19]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [23, 26]⟩, ⟨.or, [42, 29]⟩, ⟨.or, [43, 31]⟩, ⟨.or, [44, 34]⟩, ⟨.or, [45, 36]⟩, ⟨.or, [46, 38]⟩, ⟨.or, [47, 41]⟩], 48⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g => (g.op matches GateOp.and || g.op matches GateOp.or) && decide (g.inputs.length ≤ 2)

theorem okB_mono (C : Circuit) (h : okB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp_all

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10260651070736356020 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨circ, okB_mono circ (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19727_aux

theorem PEqualNP.Outside.L_meta_19727 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10260651070736356020 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_19727_aux.main
