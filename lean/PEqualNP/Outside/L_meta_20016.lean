import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20016_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 7]⟩, ⟨.or, [6, 14]⟩, ⟨.or, [13, 1]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [0, 16]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [5, 15]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [4, 22]⟩, ⟨.or, [3, 13]⟩, ⟨.and, [24, 21]⟩, ⟨.or, [25, 24]⟩, ⟨.or, [16, 10]⟩, ⟨.or, [22, 20]⟩, ⟨.or, [10, 27]⟩, ⟨.and, [28, 19]⟩, ⟨.or, [26, 23]⟩, ⟨.and, [30, 32]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [34, 29]⟩, ⟨.or, [21, 1]⟩, ⟨.and, [36, 17]⟩, ⟨.and, [25, 4]⟩, ⟨.or, [38, 37]⟩, ⟨.or, [33, 39]⟩, ⟨.or, [40, 31]⟩, ⟨.or, [41, 35]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7067567463510332610 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20016_aux

theorem PEqualNP.Outside.L_meta_20016 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7067567463510332610 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20016_aux.main
