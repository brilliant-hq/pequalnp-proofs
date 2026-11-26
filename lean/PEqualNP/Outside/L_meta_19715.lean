import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19715

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [10, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [19, 22]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [16, 24]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [18, 27]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [17, 29]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [31, 32]⟩, ⟨.and, [0, 20]⟩, ⟨.and, [1, 21]⟩, ⟨.and, [2, 23]⟩, ⟨.and, [3, 25]⟩, ⟨.and, [4, 26]⟩, ⟨.and, [5, 28]⟩, ⟨.and, [6, 30]⟩, ⟨.and, [7, 33]⟩, ⟨.or, [41, 40]⟩, ⟨.or, [42, 39]⟩, ⟨.or, [43, 38]⟩, ⟨.or, [44, 37]⟩, ⟨.or, [45, 36]⟩, ⟨.or, [46, 35]⟩, ⟨.or, [47, 34]⟩], 48⟩

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

end PEqualNP.Outside.L_meta_19715

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19715 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7598353482589123020 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_meta_19715.witness, PEqualNP.Outside.L_meta_19715.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
