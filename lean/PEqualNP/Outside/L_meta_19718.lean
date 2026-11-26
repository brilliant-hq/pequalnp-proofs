import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19718

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [10, 12]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [8, 20]⟩, ⟨.or, [15, 20]⟩, ⟨.or, [16, 21]⟩, ⟨.or, [18, 21]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [19, 27]⟩, ⟨.or, [18, 22]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [18, 30]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [22, 32]⟩, ⟨.and, [0, 23]⟩, ⟨.and, [1, 24]⟩, ⟨.and, [2, 25]⟩, ⟨.and, [3, 26]⟩, ⟨.and, [4, 28]⟩, ⟨.and, [5, 29]⟩, ⟨.and, [6, 31]⟩, ⟨.and, [7, 33]⟩, ⟨.or, [41, 40]⟩, ⟨.or, [42, 39]⟩, ⟨.or, [43, 38]⟩, ⟨.or, [44, 37]⟩, ⟨.or, [45, 36]⟩, ⟨.or, [46, 35]⟩, ⟨.or, [47, 34]⟩], 48⟩

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

end PEqualNP.Outside.L_meta_19718

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19718 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7482418488621907005 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_meta_19718.witness, PEqualNP.Outside.L_meta_19718.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
