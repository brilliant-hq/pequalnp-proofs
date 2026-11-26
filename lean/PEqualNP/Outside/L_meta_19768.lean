import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [11, 12]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [8, 18]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [19, 23]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [25, 26]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [20, 28]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [17, 30]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [20, 33]⟩, ⟨.and, [0, 21]⟩, ⟨.and, [1, 22]⟩, ⟨.and, [2, 24]⟩, ⟨.and, [3, 27]⟩, ⟨.and, [4, 29]⟩, ⟨.and, [5, 31]⟩, ⟨.and, [6, 32]⟩, ⟨.and, [7, 34]⟩, ⟨.or, [42, 41]⟩, ⟨.or, [43, 40]⟩, ⟨.or, [44, 39]⟩, ⟨.or, [45, 38]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 36]⟩, ⟨.or, [48, 35]⟩], 49⟩

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

end PEqualNP.Outside.L_meta_19768

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19768 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5748802764708593400 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨PEqualNP.Outside.L_meta_19768.witness, PEqualNP.Outside.L_meta_19768.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
