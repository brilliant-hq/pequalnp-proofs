import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23051_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [7, 0]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [13, 6]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [15, 5]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [5, 0]⟩, ⟨.or, [18, 17]⟩, ⟨.and, [17, 18]⟩, ⟨.and, [14, 3]⟩, ⟨.and, [12, 20]⟩, ⟨.or, [21, 22]⟩, ⟨.or, [24, 23]⟩], 25⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948534 : ℕ).testBit (6 * u.val + v.val)) 16 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23051_aux

theorem PEqualNP.Outside.L_meta_23051 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948534 : ℕ).testBit (6 * u.val + v.val)) 16) := by
  exact PEqualNP.Outside.L_meta_23051_aux.main
