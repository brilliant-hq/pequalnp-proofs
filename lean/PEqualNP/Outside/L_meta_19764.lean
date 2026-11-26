import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19764_aux

def witness : Circuit :=
  ⟨[⟨.or, [11, 8]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [13, 0]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [18, 4]⟩, ⟨.or, [12, 19]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [21, 8]⟩, ⟨.or, [21, 9]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [22, 7]⟩, ⟨.or, [5, 14]⟩, ⟨.and, [20, 27]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [30, 3]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [21, 20]⟩, ⟨.and, [26, 25]⟩, ⟨.and, [16, 31]⟩, ⟨.or, [11, 24]⟩, ⟨.and, [9, 33]⟩, ⟨.and, [6, 36]⟩, ⟨.or, [35, 37]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [28, 19]⟩, ⟨.or, [10, 41]⟩, ⟨.or, [34, 40]⟩, ⟨.and, [42, 32]⟩, ⟨.or, [44, 29]⟩, ⟨.or, [45, 43]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_19764_aux

open PEqualNP.Outside.L_meta_19764_aux in
theorem PEqualNP.Outside.L_meta_19764 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
