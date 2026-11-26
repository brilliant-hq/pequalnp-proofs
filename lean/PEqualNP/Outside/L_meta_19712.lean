import PEqualNP.Defs

/-! Proof skeleton in the form of upstream `L_meta_19800` (Legoshi): an explicit AND/OR circuit of
fan-in two with 26 gates, checked by `decide`. -/

namespace PEqualNP.Outside.L_meta_19712_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [14, 7]⟩, ⟨.or, [16, 4]⟩, ⟨.or, [17, 15]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [15, 13]⟩, ⟨.and, [8, 6]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [0, 19]⟩, ⟨.or, [20, 13]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [23, 24]⟩, ⟨.and, [29, 25]⟩, ⟨.or, [21, 0]⟩, ⟨.or, [31, 11]⟩, ⟨.and, [19, 18]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [33, 22]⟩, ⟨.and, [32, 34]⟩, ⟨.or, [30, 36]⟩, ⟨.or, [26, 27]⟩, ⟨.or, [35, 37]⟩, ⟨.and, [38, 28]⟩, ⟨.or, [39, 40]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (838035264769107540 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19712_aux

theorem PEqualNP.Outside.L_meta_19712 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (838035264769107540 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_19712_aux.main
