import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19794

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [18, 23]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [18, 25]⟩, ⟨.or, [4, 19]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [29, 30]⟩, ⟨.or, [0, 19]⟩, ⟨.and, [20, 8]⟩, ⟨.and, [22, 9]⟩, ⟨.and, [24, 10]⟩, ⟨.and, [26, 11]⟩, ⟨.and, [27, 12]⟩, ⟨.and, [28, 13]⟩, ⟨.and, [31, 14]⟩, ⟨.and, [32, 15]⟩, ⟨.or, [40, 39]⟩, ⟨.or, [41, 38]⟩, ⟨.or, [42, 37]⟩, ⟨.or, [43, 36]⟩, ⟨.or, [44, 35]⟩, ⟨.or, [45, 34]⟩, ⟨.or, [46, 33]⟩], 47⟩

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

end PEqualNP.Outside.L_meta_19794

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19794 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15289266858240601290 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_meta_19794.witness, PEqualNP.Outside.L_meta_19794.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
