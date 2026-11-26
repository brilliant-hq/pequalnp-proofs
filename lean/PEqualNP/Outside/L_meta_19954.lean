import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19954_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [10, 7]⟩, ⟨.or, [12, 5]⟩, ⟨.or, [14, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [9, 19]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [21, 3]⟩, ⟨.or, [4, 22]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [26, 16]⟩, ⟨.or, [22, 2]⟩, ⟨.and, [27, 24]⟩, ⟨.or, [3, 17]⟩, ⟨.or, [28, 11]⟩, ⟨.and, [20, 4]⟩, ⟨.or, [20, 18]⟩, ⟨.and, [30, 33]⟩, ⟨.or, [23, 15]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [31, 25]⟩, ⟨.or, [37, 29]⟩, ⟨.and, [35, 36]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [40, 32]⟩, ⟨.or, [34, 41]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3537932711340590220 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19954_aux

theorem PEqualNP.Outside.L_meta_19954 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3537932711340590220 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_19954_aux.main
