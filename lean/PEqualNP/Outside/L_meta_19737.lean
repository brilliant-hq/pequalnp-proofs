import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19737

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [1, 7]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [2, 16]⟩, ⟨.or, [5, 17]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [18, 21]⟩, ⟨.or, [3, 19]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [17, 24]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [2, 20]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [28, 29]⟩, ⟨.or, [5, 19]⟩, ⟨.or, [3, 20]⟩, ⟨.and, [22, 8]⟩, ⟨.and, [23, 9]⟩, ⟨.and, [25, 10]⟩, ⟨.and, [26, 11]⟩, ⟨.and, [27, 12]⟩, ⟨.and, [30, 13]⟩, ⟨.and, [31, 14]⟩, ⟨.and, [32, 15]⟩, ⟨.or, [40, 39]⟩, ⟨.or, [41, 38]⟩, ⟨.or, [42, 37]⟩, ⟨.or, [43, 36]⟩, ⟨.or, [44, 35]⟩, ⟨.or, [45, 34]⟩, ⟨.or, [46, 33]⟩], 47⟩

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

end PEqualNP.Outside.L_meta_19737

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19737 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5662696764710545965 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_meta_19737.witness, PEqualNP.Outside.L_meta_19737.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
