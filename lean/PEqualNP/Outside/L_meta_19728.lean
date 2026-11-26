import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19728

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [11, 15]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [20, 26]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [15, 21]⟩, ⟨.or, [12, 21]⟩, ⟨.or, [10, 18]⟩, ⟨.or, [20, 31]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [19, 33]⟩, ⟨.and, [0, 24]⟩, ⟨.and, [1, 25]⟩, ⟨.and, [2, 27]⟩, ⟨.and, [3, 28]⟩, ⟨.and, [4, 29]⟩, ⟨.and, [5, 30]⟩, ⟨.and, [6, 32]⟩, ⟨.and, [7, 34]⟩, ⟨.or, [42, 41]⟩, ⟨.or, [43, 40]⟩, ⟨.or, [44, 39]⟩, ⟨.or, [45, 38]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 36]⟩, ⟨.or, [48, 35]⟩], 49⟩

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

end PEqualNP.Outside.L_meta_19728

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19728 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13346266753825361370 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  ⟨PEqualNP.Outside.L_meta_19728.witness, PEqualNP.Outside.L_meta_19728.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
