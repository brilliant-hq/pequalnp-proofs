import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19949_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 11]⟩, ⟨.or, [15, 9]⟩, ⟨.or, [16, 9]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [25, 23]⟩, ⟨.or, [19, 14]⟩, ⟨.or, [27, 16]⟩, ⟨.or, [17, 25]⟩, ⟨.or, [24, 13]⟩, ⟨.and, [22, 30]⟩, ⟨.or, [15, 23]⟩, ⟨.or, [19, 28]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [20, 35]⟩, ⟨.or, [31, 20]⟩, ⟨.or, [21, 18]⟩, ⟨.and, [24, 36]⟩, ⟨.and, [33, 37]⟩, ⟨.or, [40, 32]⟩, ⟨.and, [29, 26]⟩, ⟨.and, [38, 34]⟩, ⟨.or, [39, 43]⟩, ⟨.or, [42, 44]⟩, ⟨.or, [41, 45]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4319635817910669180 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19949_aux

theorem PEqualNP.Outside.L_meta_19949 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4319635817910669180 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_19949_aux.main
