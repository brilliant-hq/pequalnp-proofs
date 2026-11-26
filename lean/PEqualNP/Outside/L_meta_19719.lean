import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19719

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [9, 15]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [13, 22]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [14, 26]⟩, ⟨.or, [15, 18]⟩, ⟨.and, [0, 19]⟩, ⟨.and, [1, 20]⟩, ⟨.and, [2, 21]⟩, ⟨.and, [3, 23]⟩, ⟨.and, [4, 24]⟩, ⟨.and, [5, 25]⟩, ⟨.and, [6, 27]⟩, ⟨.and, [7, 28]⟩, ⟨.or, [36, 35]⟩, ⟨.or, [37, 34]⟩, ⟨.or, [38, 33]⟩, ⟨.or, [39, 32]⟩, ⟨.or, [40, 31]⟩, ⟨.or, [41, 30]⟩, ⟨.or, [42, 29]⟩], 43⟩

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

end PEqualNP.Outside.L_meta_19719

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19719 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9901191629971542690 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_meta_19719.witness, PEqualNP.Outside.L_meta_19719.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
