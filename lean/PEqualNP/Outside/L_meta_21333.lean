import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21333_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [7, 2]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [4, 1]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [13, 9]⟩, ⟨.and, [15, 16]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [17, 18]⟩], 19⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (105912 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21333_aux

theorem PEqualNP.Outside.L_meta_21333 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (105912 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  PEqualNP.Outside.L_meta_21333_aux.main
