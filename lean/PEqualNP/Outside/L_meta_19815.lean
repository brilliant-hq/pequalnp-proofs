import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19815_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [9, 12]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [0, 20]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [22, 18]⟩, ⟨.and, [1, 23]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [25, 16]⟩, ⟨.and, [2, 26]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [28, 16]⟩, ⟨.and, [3, 29]⟩, ⟨.or, [16, 19]⟩, ⟨.and, [4, 31]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [33, 17]⟩, ⟨.and, [5, 34]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [6, 36]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [38, 12]⟩, ⟨.or, [39, 15]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [21, 24]⟩, ⟨.or, [42, 27]⟩, ⟨.or, [43, 30]⟩, ⟨.or, [44, 32]⟩, ⟨.or, [45, 35]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 41]⟩], 48⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g => (g.op matches GateOp.and || g.op matches GateOp.or) && decide (g.inputs.length ≤ 2)

theorem okB_mono (C : Circuit) (h : okB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp_all

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10801013263263746985 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨circ, okB_mono circ (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19815_aux

theorem PEqualNP.Outside.L_meta_19815 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10801013263263746985 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_19815_aux.main
