import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19783_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [8, 9]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [14, 18]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [13, 17]⟩, ⟨.and, [1, 21]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [2, 23]⟩, ⟨.or, [11, 17]⟩, ⟨.and, [3, 25]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [27, 15]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [9, 18]⟩, ⟨.and, [5, 30]⟩, ⟨.or, [13, 16]⟩, ⟨.and, [6, 32]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [34, 14]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [37, 24]⟩, ⟨.or, [38, 26]⟩, ⟨.or, [39, 29]⟩, ⟨.or, [40, 31]⟩, ⟨.or, [41, 33]⟩, ⟨.or, [42, 36]⟩], 43⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g => (g.op matches GateOp.and || g.op matches GateOp.or) && decide (g.inputs.length ≤ 2)

theorem okB_mono (C : Circuit) (h : okB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp_all

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8080454460742251720 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨circ, okB_mono circ (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19783_aux

theorem PEqualNP.Outside.L_meta_19783 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8080454460742251720 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_19783_aux.main
