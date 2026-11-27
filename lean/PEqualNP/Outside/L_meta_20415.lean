import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20415

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [7, 10]⟩], 11⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (383 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20415

theorem PEqualNP.Outside.L_meta_20415 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (383 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  PEqualNP.Outside.L_meta_20415.main
