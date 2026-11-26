import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19775_aux

def witness : Circuit :=
  ⟨[⟨.or, [14, 4]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [3, 11]⟩, ⟨.and, [1, 14]⟩, ⟨.or, [1, 17]⟩, ⟨.or, [3, 17]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [18, 10]⟩, ⟨.or, [15, 7]⟩, ⟨.or, [5, 22]⟩, ⟨.or, [20, 25]⟩, ⟨.and, [22, 25]⟩, ⟨.or, [21, 12]⟩, ⟨.or, [0, 24]⟩, ⟨.or, [26, 2]⟩, ⟨.and, [31, 32]⟩, ⟨.or, [2, 13]⟩, ⟨.and, [30, 27]⟩, ⟨.and, [19, 28]⟩, ⟨.or, [23, 7]⟩, ⟨.and, [34, 37]⟩, ⟨.or, [36, 35]⟩, ⟨.or, [33, 39]⟩, ⟨.or, [29, 40]⟩, ⟨.or, [41, 38]⟩], 42⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : FanInTwo witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

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

end PEqualNP.Outside.L_meta_19775_aux

open PEqualNP.Outside.L_meta_19775_aux in
theorem PEqualNP.Outside.L_meta_19775 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
