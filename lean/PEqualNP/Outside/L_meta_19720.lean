import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19720_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def okGate : Gate → Bool
  | ⟨.and, l⟩ => decide (l.length ≤ 2)
  | ⟨.or, l⟩ => decide (l.length ≤ 2)
  | _ => false

theorem okGate_spec (g : Gate) (h : okGate g = true) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  rcases g with ⟨op, l⟩
  cases op <;> simp_all [okGate]

def circ : Circuit := ⟨[⟨.or, [8, 14]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [10, 20]⟩, ⟨.and, [0, 21]⟩, ⟨.or, [11, 19]⟩, ⟨.and, [1, 23]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [25, 16]⟩, ⟨.and, [2, 26]⟩, ⟨.or, [8, 19]⟩, ⟨.and, [3, 28]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [30, 17]⟩, ⟨.and, [4, 31]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [33, 16]⟩, ⟨.and, [5, 34]⟩, ⟨.or, [9, 20]⟩, ⟨.and, [6, 36]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [7, 38]⟩, ⟨.or, [22, 24]⟩, ⟨.or, [40, 27]⟩, ⟨.or, [41, 29]⟩, ⟨.or, [42, 32]⟩, ⟨.or, [43, 35]⟩, ⟨.or, [44, 37]⟩, ⟨.or, [45, 39]⟩], 46⟩

theorem circ_ok : circ.gates.all okGate = true := by decide

end PEqualNP.Outside.L_meta_19720_aux

open PEqualNP.Outside.L_meta_19720_aux in
theorem PEqualNP.Outside.L_meta_19720 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7582498071666593340 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨circ, fun g hg => okGate_spec g (List.all_eq_true.mp circ_ok g hg), by decide, by decide +kernel⟩
