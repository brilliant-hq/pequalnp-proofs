import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19779

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [9, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [10, 20]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [18, 23]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [18, 25]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [19, 27]⟩, ⟨.or, [15, 21]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [19, 30]⟩, ⟨.or, [13, 21]⟩, ⟨.or, [12, 20]⟩, ⟨.and, [0, 22]⟩, ⟨.and, [1, 24]⟩, ⟨.and, [2, 26]⟩, ⟨.and, [3, 28]⟩, ⟨.and, [4, 29]⟩, ⟨.and, [5, 31]⟩, ⟨.and, [6, 32]⟩, ⟨.and, [7, 33]⟩, ⟨.or, [41, 40]⟩, ⟨.or, [42, 39]⟩, ⟨.or, [43, 38]⟩, ⟨.or, [44, 37]⟩, ⟨.or, [45, 36]⟩, ⟨.or, [46, 35]⟩, ⟨.or, [47, 34]⟩], 48⟩

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

end PEqualNP.Outside.L_meta_19779

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19779 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17455334905265877990 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_meta_19779.witness, PEqualNP.Outside.L_meta_19779.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
