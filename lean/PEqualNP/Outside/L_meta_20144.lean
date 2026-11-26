import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20144_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 14]⟩, ⟨.or, [15, 8]⟩, ⟨.or, [0, 13]⟩, ⟨.and, [5, 17]⟩, ⟨.or, [19, 7]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [20, 12]⟩, ⟨.or, [1, 23]⟩, ⟨.or, [23, 10]⟩, ⟨.or, [9, 18]⟩, ⟨.or, [4, 25]⟩, ⟨.or, [5, 22]⟩, ⟨.or, [10, 22]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [16, 28]⟩, ⟨.or, [26, 31]⟩, ⟨.and, [4, 25]⟩, ⟨.and, [21, 32]⟩, ⟨.or, [27, 16]⟩, ⟨.and, [9, 31]⟩, ⟨.or, [14, 24]⟩, ⟨.or, [18, 30]⟩, ⟨.and, [37, 29]⟩, ⟨.and, [38, 35]⟩, ⟨.or, [34, 39]⟩, ⟨.or, [40, 36]⟩, ⟨.or, [33, 42]⟩, ⟨.or, [43, 41]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11914988824647881820 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20144_aux

theorem PEqualNP.Outside.L_meta_20144 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11914988824647881820 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_20144_aux.main
