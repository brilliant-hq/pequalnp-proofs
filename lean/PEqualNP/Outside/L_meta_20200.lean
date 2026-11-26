import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20200_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- An AND/OR circuit found by a search program outside this file; its last gate is the output.
def C_ : Circuit := ⟨[⟨.or, [3, 15]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [4, 18]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [9, 0]⟩, ⟨.and, [22, 20]⟩, ⟨.or, [11, 23]⟩, ⟨.or, [1, 24]⟩, ⟨.or, [8, 20]⟩, ⟨.or, [16, 8]⟩, ⟨.or, [26, 22]⟩, ⟨.or, [11, 19]⟩, ⟨.or, [1, 27]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [30, 18]⟩, ⟨.or, [25, 21]⟩, ⟨.and, [31, 15]⟩, ⟨.or, [19, 27]⟩, ⟨.or, [0, 21]⟩, ⟨.or, [34, 17]⟩, ⟨.and, [32, 29]⟩, ⟨.or, [38, 37]⟩, ⟨.or, [36, 35]⟩, ⟨.and, [40, 39]⟩, ⟨.and, [33, 28]⟩, ⟨.or, [41, 42]⟩], 43⟩

def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14215526027697465180 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20200_aux

theorem PEqualNP.Outside.L_meta_20200 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14215526027697465180 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20200_aux.main
