import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19721

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [10, 11]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [15, 21]⟩, ⟨.or, [26, 27]⟩, ⟨.or, [8, 22]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [12, 22]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 21]⟩, ⟨.or, [32, 33]⟩, ⟨.and, [0, 23]⟩, ⟨.and, [1, 24]⟩, ⟨.and, [2, 25]⟩, ⟨.and, [3, 28]⟩, ⟨.and, [4, 29]⟩, ⟨.and, [5, 30]⟩, ⟨.and, [6, 31]⟩, ⟨.and, [7, 34]⟩, ⟨.or, [42, 41]⟩, ⟨.or, [43, 40]⟩, ⟨.or, [44, 39]⟩, ⟨.or, [45, 38]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 36]⟩, ⟨.or, [48, 35]⟩], 49⟩

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

end PEqualNP.Outside.L_meta_19721

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19721 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4319635817910669180 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨PEqualNP.Outside.L_meta_19721.witness, PEqualNP.Outside.L_meta_19721.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
