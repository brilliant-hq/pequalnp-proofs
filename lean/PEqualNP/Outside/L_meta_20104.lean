import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20104

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [4, 17]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [6, 19]⟩, ⟨.or, [6, 18]⟩, ⟨.or, [5, 21]⟩, ⟨.or, [17, 22]⟩, ⟨.or, [0, 20]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [26, 27]⟩, ⟨.or, [4, 20]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [1, 21]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [22, 32]⟩, ⟨.and, [8, 23]⟩, ⟨.and, [9, 24]⟩, ⟨.and, [10, 25]⟩, ⟨.and, [11, 28]⟩, ⟨.and, [12, 29]⟩, ⟨.and, [13, 30]⟩, ⟨.and, [14, 31]⟩, ⟨.and, [15, 33]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [42, 36]⟩, ⟨.or, [43, 37]⟩, ⟨.or, [44, 38]⟩, ⟨.or, [45, 39]⟩, ⟨.or, [46, 40]⟩, ⟨.or, [47, 41]⟩], 48⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11442406341415304295 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20104

theorem PEqualNP.Outside.L_meta_20104 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11442406341415304295 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_20104.main
