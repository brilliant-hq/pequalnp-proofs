import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19792

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 7]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [4, 16]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [6, 16]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [5, 16]⟩, ⟨.or, [19, 25]⟩, ⟨.or, [2, 17]⟩, ⟨.or, [19, 27]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [7, 18]⟩, ⟨.or, [19, 30]⟩, ⟨.or, [6, 21]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [0, 21]⟩, ⟨.and, [24, 8]⟩, ⟨.and, [26, 9]⟩, ⟨.and, [28, 10]⟩, ⟨.and, [29, 11]⟩, ⟨.and, [31, 12]⟩, ⟨.and, [32, 13]⟩, ⟨.and, [33, 14]⟩, ⟨.and, [34, 15]⟩, ⟨.or, [42, 41]⟩, ⟨.or, [43, 40]⟩, ⟨.or, [44, 39]⟩, ⟨.or, [45, 38]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 36]⟩, ⟨.or, [48, 35]⟩], 49⟩

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

end PEqualNP.Outside.L_meta_19792

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19792 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6572913902839198155 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨PEqualNP.Outside.L_meta_19792.witness, PEqualNP.Outside.L_meta_19792.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
