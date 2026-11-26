import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20010_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [2, 8]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [4, 14]⟩, ⟨.and, [14, 4]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [21, 17]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [15, 1]⟩, ⟨.or, [25, 24]⟩, ⟨.and, [26, 23]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [20, 28]⟩, ⟨.and, [30, 32]⟩, ⟨.or, [17, 26]⟩, ⟨.or, [24, 24]⟩, ⟨.and, [34, 29]⟩, ⟨.or, [9, 35]⟩, ⟨.or, [37, 23]⟩, ⟨.or, [31, 16]⟩, ⟨.or, [18, 38]⟩, ⟨.or, [40, 28]⟩, ⟨.or, [36, 33]⟩, ⟨.and, [41, 39]⟩, ⟨.or, [27, 42]⟩, ⟨.or, [44, 43]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16823704204436992830 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20010_aux

theorem PEqualNP.Outside.L_meta_20010 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16823704204436992830 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_20010_aux.main
