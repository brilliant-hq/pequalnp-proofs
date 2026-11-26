import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19754

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [12, 13]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [15, 22]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [10, 24]⟩, ⟨.or, [10, 18]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [12, 18]⟩, ⟨.and, [0, 19]⟩, ⟨.and, [1, 20]⟩, ⟨.and, [2, 21]⟩, ⟨.and, [3, 23]⟩, ⟨.and, [4, 25]⟩, ⟨.and, [5, 26]⟩, ⟨.and, [6, 27]⟩, ⟨.and, [7, 28]⟩, ⟨.or, [36, 35]⟩, ⟨.or, [37, 34]⟩, ⟨.or, [38, 33]⟩, ⟨.or, [39, 32]⟩, ⟨.or, [40, 31]⟩, ⟨.or, [41, 30]⟩, ⟨.or, [42, 29]⟩], 43⟩

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

end PEqualNP.Outside.L_meta_19754

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19754 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14991291321697978680 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_meta_19754.witness, PEqualNP.Outside.L_meta_19754.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
