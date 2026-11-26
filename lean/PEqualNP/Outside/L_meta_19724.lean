import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19724_aux

def witness : Circuit :=
  ⟨[⟨.or, [11, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [16, 6]⟩, ⟨.or, [11, 19]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [10, 18]⟩, ⟨.and, [20, 22]⟩, ⟨.or, [15, 4]⟩, ⟨.or, [7, 18]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [21, 27]⟩, ⟨.or, [12, 24]⟩, ⟨.or, [5, 22]⟩, ⟨.and, [4, 15]⟩, ⟨.and, [23, 30]⟩, ⟨.and, [26, 28]⟩, ⟨.and, [17, 10]⟩, ⟨.or, [25, 14]⟩, ⟨.or, [21, 6]⟩, ⟨.or, [25, 30]⟩, ⟨.and, [35, 36]⟩, ⟨.or, [32, 29]⟩, ⟨.or, [39, 31]⟩, ⟨.or, [33, 38]⟩, ⟨.or, [19, 37]⟩, ⟨.or, [2, 40]⟩, ⟨.and, [42, 43]⟩, ⟨.or, [34, 41]⟩, ⟨.or, [45, 44]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_19724_aux

open PEqualNP.Outside.L_meta_19724_aux in
theorem PEqualNP.Outside.L_meta_19724 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
