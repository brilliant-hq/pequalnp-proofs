import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19550

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [9, 11]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [16, 21]⟩, ⟨.or, [11, 20]⟩, ⟨.or, [9, 19]⟩, ⟨.or, [14, 24]⟩, ⟨.or, [10, 21]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [13, 26]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [10, 20]⟩, ⟨.or, [18, 17]⟩, ⟨.and, [0, 31]⟩, ⟨.and, [1, 29]⟩, ⟨.and, [2, 22]⟩, ⟨.and, [3, 27]⟩, ⟨.and, [4, 30]⟩, ⟨.and, [5, 23]⟩, ⟨.and, [6, 28]⟩, ⟨.and, [7, 25]⟩, ⟨.or, [32, 33]⟩, ⟨.or, [40, 34]⟩, ⟨.or, [41, 35]⟩, ⟨.or, [42, 36]⟩, ⟨.or, [43, 37]⟩, ⟨.or, [44, 38]⟩, ⟨.or, [45, 39]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0xc3b478740f9a8b65 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨circ, monoTwoB_sound circ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19550

theorem PEqualNP.Outside.L_meta_19550 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0xc3b478740f9a8b65 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_19550.main
