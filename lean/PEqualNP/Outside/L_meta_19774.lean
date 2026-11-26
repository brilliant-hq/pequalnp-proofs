import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19774_aux

def witness : Circuit :=
  ⟨[⟨.or, [13, 6]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [14, 4]⟩, ⟨.or, [9, 18]⟩, ⟨.or, [12, 3]⟩, ⟨.or, [22, 5]⟩, ⟨.or, [5, 17]⟩, ⟨.or, [11, 0]⟩, ⟨.or, [6, 17]⟩, ⟨.or, [16, 25]⟩, ⟨.or, [9, 19]⟩, ⟨.or, [20, 25]⟩, ⟨.or, [27, 21]⟩, ⟨.or, [31, 22]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [28, 21]⟩, ⟨.and, [32, 19]⟩, ⟨.and, [30, 33]⟩, ⟨.and, [26, 29]⟩, ⟨.or, [23, 21]⟩, ⟨.or, [36, 23]⟩, ⟨.or, [26, 39]⟩, ⟨.and, [38, 24]⟩, ⟨.or, [35, 41]⟩, ⟨.or, [34, 37]⟩, ⟨.and, [43, 40]⟩, ⟨.or, [42, 44]⟩], 45⟩

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

end PEqualNP.Outside.L_meta_19774_aux

open PEqualNP.Outside.L_meta_19774_aux in
theorem PEqualNP.Outside.L_meta_19774 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
