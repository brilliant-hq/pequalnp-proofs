import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19711

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [8, 9]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [10, 18]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [19, 24]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [27, 28]⟩, ⟨.or, [15, 18]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [20, 31]⟩, ⟨.and, [0, 21]⟩, ⟨.and, [1, 22]⟩, ⟨.and, [2, 23]⟩, ⟨.and, [3, 25]⟩, ⟨.and, [4, 26]⟩, ⟨.and, [5, 29]⟩, ⟨.and, [6, 30]⟩, ⟨.and, [7, 32]⟩, ⟨.or, [40, 39]⟩, ⟨.or, [41, 38]⟩, ⟨.or, [42, 37]⟩, ⟨.or, [43, 36]⟩, ⟨.or, [44, 35]⟩, ⟨.or, [45, 34]⟩, ⟨.or, [46, 33]⟩], 47⟩

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

end PEqualNP.Outside.L_meta_19711

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19711 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17339788871490640935 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_meta_19711.witness, PEqualNP.Outside.L_meta_19711.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
