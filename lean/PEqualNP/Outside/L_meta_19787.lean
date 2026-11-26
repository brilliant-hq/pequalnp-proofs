import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19787

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [8, 11]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [13, 19]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [13, 20]⟩, ⟨.or, [8, 20]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 18]⟩, ⟨.or, [25, 26]⟩, ⟨.or, [9, 21]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [29, 30]⟩, ⟨.or, [14, 21]⟩, ⟨.or, [10, 20]⟩, ⟨.and, [0, 22]⟩, ⟨.and, [1, 23]⟩, ⟨.and, [2, 24]⟩, ⟨.and, [3, 27]⟩, ⟨.and, [4, 28]⟩, ⟨.and, [5, 31]⟩, ⟨.and, [6, 32]⟩, ⟨.and, [7, 33]⟩, ⟨.or, [41, 40]⟩, ⟨.or, [42, 39]⟩, ⟨.or, [43, 38]⟩, ⟨.or, [44, 37]⟩, ⟨.or, [45, 36]⟩, ⟨.or, [46, 35]⟩, ⟨.or, [47, 34]⟩], 48⟩

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

end PEqualNP.Outside.L_meta_19787

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19787 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15451209511025767005 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_meta_19787.witness, PEqualNP.Outside.L_meta_19787.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
