import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19749

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [10, 11]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [15, 18]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [19, 25]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [28, 29]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [21, 32]⟩, ⟨.or, [16, 21]⟩, ⟨.and, [0, 23]⟩, ⟨.and, [1, 24]⟩, ⟨.and, [2, 26]⟩, ⟨.and, [3, 27]⟩, ⟨.and, [4, 30]⟩, ⟨.and, [5, 31]⟩, ⟨.and, [6, 33]⟩, ⟨.and, [7, 34]⟩, ⟨.or, [42, 41]⟩, ⟨.or, [43, 40]⟩, ⟨.or, [44, 39]⟩, ⟨.or, [45, 38]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 36]⟩, ⟨.or, [48, 35]⟩], 49⟩

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

end PEqualNP.Outside.L_meta_19749

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19749 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17069659891248394590 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨PEqualNP.Outside.L_meta_19749.witness, PEqualNP.Outside.L_meta_19749.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
