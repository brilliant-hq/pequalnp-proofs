import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19891_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [14, 3]⟩, ⟨.or, [7, 15]⟩, ⟨.or, [2, 13]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [5, 18]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [21, 10]⟩, ⟨.or, [5, 19]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [12, 22]⟩, ⟨.or, [16, 11]⟩, ⟨.or, [2, 26]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [27, 17]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [29, 27]⟩, ⟨.or, [4, 29]⟩, ⟨.or, [17, 13]⟩, ⟨.or, [19, 32]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [31, 36]⟩, ⟨.and, [34, 35]⟩, ⟨.and, [33, 23]⟩, ⟨.and, [24, 37]⟩, ⟨.or, [30, 4]⟩, ⟨.and, [41, 28]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [43, 42]⟩, ⟨.or, [40, 44]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6623703746638232805 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19891_aux

theorem PEqualNP.Outside.L_meta_19891 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6623703746638232805 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  PEqualNP.Outside.L_meta_19891_aux.main
