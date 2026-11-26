import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19748_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def okGate : Gate → Bool
  | ⟨.and, l⟩ => decide (l.length ≤ 2)
  | ⟨.or, l⟩ => decide (l.length ≤ 2)
  | _ => false

theorem okGate_spec (g : Gate) (h : okGate g = true) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  rcases g with ⟨op, l⟩
  cases op <;> simp_all [okGate]

def circ : Circuit := ⟨[⟨.or, [8, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [9, 16]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [10, 16]⟩, ⟨.and, [1, 21]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [23, 13]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [15, 17]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [15, 18]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [9, 17]⟩, ⟨.and, [5, 30]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [32, 15]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [12, 18]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [37, 25]⟩, ⟨.or, [38, 27]⟩, ⟨.or, [39, 29]⟩, ⟨.or, [40, 31]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 36]⟩], 43⟩

theorem circ_ok : circ.gates.all okGate = true := by decide

end PEqualNP.Outside.L_meta_19748_aux

open PEqualNP.Outside.L_meta_19748_aux in
theorem PEqualNP.Outside.L_meta_19748 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8124800356567354635 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨circ, fun g hg => okGate_spec g (List.all_eq_true.mp circ_ok g hg), by decide, by decide +kernel⟩
