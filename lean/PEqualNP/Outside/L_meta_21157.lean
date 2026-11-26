import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21157_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [4, 14]⟩, ⟨.or, [13, 15]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [16, 17]⟩], 18⟩

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

end PEqualNP.Outside.L_meta_21157_aux

open PEqualNP.Outside.L_meta_21157_aux

theorem PEqualNP.Outside.L_meta_21157 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40190 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
