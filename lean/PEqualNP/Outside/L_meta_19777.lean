import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19777

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [10, 13]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [8, 18]⟩, ⟨.or, [10, 19]⟩, ⟨.or, [11, 19]⟩, ⟨.and, [0, 20]⟩, ⟨.and, [1, 21]⟩, ⟨.and, [2, 22]⟩, ⟨.and, [3, 23]⟩, ⟨.and, [4, 24]⟩, ⟨.and, [5, 25]⟩, ⟨.and, [6, 26]⟩, ⟨.and, [7, 27]⟩, ⟨.or, [35, 34]⟩, ⟨.or, [36, 33]⟩, ⟨.or, [37, 32]⟩, ⟨.or, [38, 31]⟩, ⟨.or, [39, 30]⟩, ⟨.or, [40, 29]⟩, ⟨.or, [41, 28]⟩], 42⟩

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

end PEqualNP.Outside.L_meta_19777

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19777 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14466700110149527140 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨PEqualNP.Outside.L_meta_19777.witness, PEqualNP.Outside.L_meta_19777.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
