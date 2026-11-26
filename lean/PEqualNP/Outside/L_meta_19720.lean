import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19720

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [11, 13]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [10, 19]⟩, ⟨.or, [11, 20]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [18, 23]⟩, ⟨.or, [8, 20]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [17, 26]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [18, 28]⟩, ⟨.or, [9, 19]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [0, 21]⟩, ⟨.and, [1, 22]⟩, ⟨.and, [2, 24]⟩, ⟨.and, [3, 25]⟩, ⟨.and, [4, 27]⟩, ⟨.and, [5, 29]⟩, ⟨.and, [6, 30]⟩, ⟨.and, [7, 31]⟩, ⟨.or, [39, 38]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [41, 36]⟩, ⟨.or, [42, 35]⟩, ⟨.or, [43, 34]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [45, 32]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_19720

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19720 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7582498071666593340 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨PEqualNP.Outside.L_meta_19720.witness, PEqualNP.Outside.L_meta_19720.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
