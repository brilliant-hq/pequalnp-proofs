import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19781

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [2, 7]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [3, 17]⟩, ⟨.or, [4, 16]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [1, 19]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [17, 24]⟩, ⟨.or, [6, 19]⟩, ⟨.or, [0, 20]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [21, 28]⟩, ⟨.or, [1, 20]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [22, 15]⟩, ⟨.and, [23, 11]⟩, ⟨.and, [25, 14]⟩, ⟨.and, [26, 12]⟩, ⟨.and, [27, 13]⟩, ⟨.and, [29, 8]⟩, ⟨.and, [30, 10]⟩, ⟨.and, [31, 9]⟩, ⟨.or, [39, 38]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [41, 36]⟩, ⟨.or, [42, 35]⟩, ⟨.or, [43, 34]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [45, 32]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_19781

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19781 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16488339210259238520 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨PEqualNP.Outside.L_meta_19781.witness, PEqualNP.Outside.L_meta_19781.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
