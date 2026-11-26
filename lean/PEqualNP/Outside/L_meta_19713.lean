import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19713

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [12, 13]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [18, 21]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [18, 23]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [15, 20]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [16, 27]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [16, 30]⟩, ⟨.or, [8, 20]⟩, ⟨.and, [0, 22]⟩, ⟨.and, [1, 24]⟩, ⟨.and, [2, 25]⟩, ⟨.and, [3, 26]⟩, ⟨.and, [4, 28]⟩, ⟨.and, [5, 29]⟩, ⟨.and, [6, 31]⟩, ⟨.and, [7, 32]⟩, ⟨.or, [40, 39]⟩, ⟨.or, [41, 38]⟩, ⟨.or, [42, 37]⟩, ⟨.or, [43, 36]⟩, ⟨.or, [44, 35]⟩, ⟨.or, [45, 34]⟩, ⟨.or, [46, 33]⟩], 47⟩

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

end PEqualNP.Outside.L_meta_19713

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19713 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5420442459739364580 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_meta_19713.witness, PEqualNP.Outside.L_meta_19713.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
