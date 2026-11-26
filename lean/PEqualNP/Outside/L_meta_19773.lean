import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19773

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [4, 17]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [6, 16]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [5, 19]⟩, ⟨.or, [1, 19]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [20, 25]⟩, ⟨.or, [3, 21]⟩, ⟨.or, [1, 21]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [17, 29]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [22, 8]⟩, ⟨.and, [23, 9]⟩, ⟨.and, [24, 10]⟩, ⟨.and, [26, 11]⟩, ⟨.and, [27, 12]⟩, ⟨.and, [28, 13]⟩, ⟨.and, [30, 14]⟩, ⟨.and, [31, 15]⟩, ⟨.or, [39, 38]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [41, 36]⟩, ⟨.or, [42, 35]⟩, ⟨.or, [43, 34]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [45, 32]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_19773

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19773 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5672340417107567985 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_meta_19773.witness, PEqualNP.Outside.L_meta_19773.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
