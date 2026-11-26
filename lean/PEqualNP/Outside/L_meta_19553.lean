import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19553

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [6, 16]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [2, 17]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [5, 18]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [4, 20]⟩, ⟨.or, [7, 20]⟩, ⟨.or, [16, 21]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [19, 27]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [21, 29]⟩, ⟨.or, [7, 18]⟩, ⟨.and, [22, 15]⟩, ⟨.and, [23, 8]⟩, ⟨.and, [24, 14]⟩, ⟨.and, [25, 11]⟩, ⟨.and, [26, 12]⟩, ⟨.and, [28, 10]⟩, ⟨.and, [30, 13]⟩, ⟨.and, [31, 9]⟩, ⟨.or, [39, 38]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [41, 36]⟩, ⟨.or, [42, 35]⟩, ⟨.or, [43, 34]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [45, 32]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_19553

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19553 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0x2e87c9d235786996 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_meta_19553.witness, PEqualNP.Outside.L_meta_19553.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
