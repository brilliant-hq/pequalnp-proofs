import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19743

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [12, 14]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [8, 18]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [19, 26]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [20, 28]⟩, ⟨.or, [18, 21]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [21, 33]⟩, ⟨.and, [3, 24]⟩, ⟨.and, [6, 25]⟩, ⟨.and, [1, 27]⟩, ⟨.and, [5, 29]⟩, ⟨.and, [7, 30]⟩, ⟨.and, [0, 31]⟩, ⟨.and, [4, 32]⟩, ⟨.and, [2, 34]⟩, ⟨.or, [42, 41]⟩, ⟨.or, [43, 40]⟩, ⟨.or, [44, 39]⟩, ⟨.or, [45, 38]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 36]⟩, ⟨.or, [48, 35]⟩], 49⟩

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

end PEqualNP.Outside.L_meta_19743

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19743 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12606226115316667695 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨PEqualNP.Outside.L_meta_19743.witness, PEqualNP.Outside.L_meta_19743.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
