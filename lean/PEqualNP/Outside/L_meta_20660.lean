import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20660

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circuit : Circuit := ⟨[⟨.or, [5, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 11]⟩, ⟨.and, [12, 13]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [14, 15]⟩], 16⟩

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

end PEqualNP.Outside.L_meta_20660

theorem PEqualNP.Outside.L_meta_20660 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (14060544 : ℕ).testBit (5 * u.val + v.val)) 7) := by
  refine ⟨PEqualNP.Outside.L_meta_20660.circuit, PEqualNP.Outside.L_meta_20660.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
