import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25005_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 11]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [10, 0]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [10, 20]⟩, ⟨.or, [15, 3]⟩, ⟨.or, [21, 8]⟩, ⟨.or, [24, 0]⟩, ⟨.and, [22, 25]⟩, ⟨.or, [17, 12]⟩, ⟨.or, [20, 21]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [26, 16]⟩, ⟨.or, [28, 30]⟩, ⟨.or, [18, 23]⟩, ⟨.or, [23, 31]⟩, ⟨.or, [30, 19]⟩, ⟨.or, [16, 29]⟩, ⟨.and, [35, 36]⟩, ⟨.and, [33, 27]⟩, ⟨.and, [34, 32]⟩, ⟨.or, [39, 37]⟩, ⟨.or, [38, 40]⟩], 41⟩

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

theorem main : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14516395958052687435 : ℕ).testBit (8 * u.val + v.val)) 26) :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_25005_aux

theorem PEqualNP.Outside.L_meta_25005 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14516395958052687435 : ℕ).testBit (8 * u.val + v.val)) 26) :=
  PEqualNP.Outside.L_meta_25005_aux.main
