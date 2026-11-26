import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20349_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def witness : Circuit :=
  ⟨[⟨.or, [2, 15]⟩,
     ⟨.or, [10, 16]⟩,
     ⟨.or, [3, 11]⟩,
     ⟨.or, [5, 9]⟩,
     ⟨.or, [0, 8]⟩,
     ⟨.or, [7, 12]⟩,
     ⟨.or, [11, 20]⟩,
     ⟨.or, [18, 21]⟩,
     ⟨.or, [13, 19]⟩,
     ⟨.or, [4, 14]⟩,
     ⟨.or, [6, 17]⟩,
     ⟨.or, [1, 22]⟩,
     ⟨.or, [1, 16]⟩,
     ⟨.or, [6, 27]⟩,
     ⟨.or, [21, 24]⟩,
     ⟨.or, [10, 29]⟩,
     ⟨.or, [23, 26]⟩,
     ⟨.or, [19, 20]⟩,
     ⟨.or, [13, 17]⟩,
     ⟨.and, [34, 18]⟩,
     ⟨.and, [28, 33]⟩,
     ⟨.and, [25, 32]⟩,
     ⟨.and, [31, 30]⟩,
     ⟨.or, [35, 36]⟩,
     ⟨.or, [37, 38]⟩,
     ⟨.or, [39, 40]⟩], 41⟩

private def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

private theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

private theorem main :
    RepSizeAtMost (fun u v : Fin 8 => (5580678593250014130 : ℕ).testBit (8 * u.val + v.val)) 26 :=
  ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20349_aux

theorem PEqualNP.Outside.L_meta_20349 :
    (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5580678593250014130 : ℕ).testBit (8 * u.val + v.val)) 26) :=
  PEqualNP.Outside.L_meta_20349_aux.main
