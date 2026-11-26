import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20123_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [11, 5]⟩, ⟨.or, [13, 2]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [17, 14]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [18, 0]⟩, ⟨.or, [18, 3]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [24, 16]⟩, ⟨.or, [21, 13]⟩, ⟨.or, [25, 3]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [22, 19]⟩, ⟨.or, [4, 26]⟩, ⟨.and, [25, 15]⟩, ⟨.or, [27, 15]⟩, ⟨.and, [28, 32]⟩, ⟨.or, [14, 21]⟩, ⟨.and, [20, 29]⟩, ⟨.or, [23, 10]⟩, ⟨.and, [36, 30]⟩, ⟨.or, [10, 34]⟩, ⟨.and, [1, 38]⟩, ⟨.or, [33, 35]⟩, ⟨.or, [40, 39]⟩, ⟨.or, [31, 37]⟩, ⟨.or, [41, 42]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8675770777096903905 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20123_aux

theorem PEqualNP.Outside.L_meta_20123 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8675770777096903905 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20123_aux.main
