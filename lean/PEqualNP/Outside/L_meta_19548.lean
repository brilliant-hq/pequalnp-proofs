import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19548

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [3, 5]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [2, 18]⟩, ⟨.or, [2, 16]⟩, ⟨.or, [0, 17]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [5, 19]⟩, ⟨.or, [0, 20]⟩, ⟨.or, [6, 19]⟩, ⟨.or, [7, 20]⟩, ⟨.or, [1, 21]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [18, 28]⟩, ⟨.or, [3, 21]⟩, ⟨.and, [22, 13]⟩, ⟨.and, [23, 14]⟩, ⟨.and, [24, 8]⟩, ⟨.and, [25, 10]⟩, ⟨.and, [26, 9]⟩, ⟨.and, [27, 12]⟩, ⟨.and, [29, 11]⟩, ⟨.and, [30, 15]⟩, ⟨.or, [38, 37]⟩, ⟨.or, [39, 36]⟩, ⟨.or, [40, 35]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 33]⟩, ⟨.or, [43, 32]⟩, ⟨.or, [44, 31]⟩], 45⟩

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

end PEqualNP.Outside.L_meta_19548

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19548 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0x4eb463b8a3475c99 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨PEqualNP.Outside.L_meta_19548.witness, PEqualNP.Outside.L_meta_19548.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
