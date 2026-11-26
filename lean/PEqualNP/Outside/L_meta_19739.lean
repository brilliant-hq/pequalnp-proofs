import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19739_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [8, 13]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [11, 16]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [21, 13]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [11, 18]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [11, 17]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [15, 17]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [30, 14]⟩, ⟨.and, [5, 31]⟩, ⟨.or, [12, 16]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [10, 18]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [37, 25]⟩, ⟨.or, [38, 27]⟩, ⟨.or, [39, 29]⟩, ⟨.or, [40, 32]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 36]⟩], 43⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g => (g.op matches GateOp.and || g.op matches GateOp.or) && decide (g.inputs.length ≤ 2)

theorem okB_mono (C : Circuit) (h : okB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp_all

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10678392892249613865 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨circ, okB_mono circ (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19739_aux

theorem PEqualNP.Outside.L_meta_19739 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10678392892249613865 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_19739_aux.main
