import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19762

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [10, 14]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [14, 21]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [15, 24]⟩, ⟨.or, [8, 17]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [15, 27]⟩, ⟨.or, [12, 16]⟩, ⟨.and, [0, 19]⟩, ⟨.and, [1, 20]⟩, ⟨.and, [2, 22]⟩, ⟨.and, [3, 23]⟩, ⟨.and, [4, 25]⟩, ⟨.and, [5, 26]⟩, ⟨.and, [6, 28]⟩, ⟨.and, [7, 29]⟩, ⟨.or, [37, 36]⟩, ⟨.or, [38, 35]⟩, ⟨.or, [39, 34]⟩, ⟨.or, [40, 33]⟩, ⟨.or, [41, 32]⟩, ⟨.or, [42, 31]⟩, ⟨.or, [43, 30]⟩], 44⟩

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

end PEqualNP.Outside.L_meta_19762

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19762 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6099045440807847450 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨PEqualNP.Outside.L_meta_19762.witness, PEqualNP.Outside.L_meta_19762.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
