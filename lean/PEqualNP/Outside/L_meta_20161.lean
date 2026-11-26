import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20161_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [7, 14]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [2, 16]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [19, 10]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [21, 22]⟩, ⟨.and, [17, 5]⟩, ⟨.or, [9, 24]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [9, 25]⟩, ⟨.or, [20, 21]⟩, ⟨.or, [17, 29]⟩, ⟨.and, [32, 26]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [34, 25]⟩, ⟨.or, [13, 35]⟩, ⟨.and, [28, 23]⟩, ⟨.and, [36, 31]⟩, ⟨.or, [34, 24]⟩, ⟨.or, [37, 27]⟩, ⟨.or, [38, 33]⟩, ⟨.or, [40, 41]⟩, ⟨.and, [30, 39]⟩, ⟨.or, [43, 42]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13467367414173452220 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20161_aux

theorem PEqualNP.Outside.L_meta_20161 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13467367414173452220 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_20161_aux.main
