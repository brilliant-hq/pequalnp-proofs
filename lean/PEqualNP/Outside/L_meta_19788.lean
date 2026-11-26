import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19788

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [9, 14]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [15, 21]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [15, 23]⟩, ⟨.or, [13, 18]⟩, ⟨.or, [9, 18]⟩, ⟨.or, [8, 17]⟩, ⟨.or, [13, 16]⟩, ⟨.and, [0, 19]⟩, ⟨.and, [1, 20]⟩, ⟨.and, [2, 22]⟩, ⟨.and, [3, 24]⟩, ⟨.and, [4, 25]⟩, ⟨.and, [5, 26]⟩, ⟨.and, [6, 27]⟩, ⟨.and, [7, 28]⟩, ⟨.or, [36, 35]⟩, ⟨.or, [37, 34]⟩, ⟨.or, [38, 33]⟩, ⟨.or, [39, 32]⟩, ⟨.or, [40, 31]⟩, ⟨.or, [41, 30]⟩, ⟨.or, [42, 29]⟩], 43⟩

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

end PEqualNP.Outside.L_meta_19788

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19788 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7067567463510332610 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_meta_19788.witness, PEqualNP.Outside.L_meta_19788.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
