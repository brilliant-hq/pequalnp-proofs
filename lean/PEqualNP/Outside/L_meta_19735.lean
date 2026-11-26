import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19735

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [10, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [18, 24]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [18, 26]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [29, 30]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [0, 20]⟩, ⟨.and, [1, 22]⟩, ⟨.and, [2, 23]⟩, ⟨.and, [3, 25]⟩, ⟨.and, [4, 27]⟩, ⟨.and, [5, 28]⟩, ⟨.and, [6, 31]⟩, ⟨.and, [7, 32]⟩, ⟨.or, [40, 39]⟩, ⟨.or, [41, 38]⟩, ⟨.or, [42, 37]⟩, ⟨.or, [43, 36]⟩, ⟨.or, [44, 35]⟩, ⟨.or, [45, 34]⟩, ⟨.or, [46, 33]⟩], 47⟩

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

end PEqualNP.Outside.L_meta_19735

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19735 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1110766810026783180 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_meta_19735.witness, PEqualNP.Outside.L_meta_19735.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
