import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19719_aux

def witness : Circuit :=
  ⟨[⟨.or, [15, 1]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [10, 2]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [18, 15]⟩, ⟨.or, [18, 10]⟩, ⟨.or, [11, 21]⟩, ⟨.or, [3, 25]⟩, ⟨.or, [18, 26]⟩, ⟨.or, [27, 17]⟩, ⟨.and, [18, 14]⟩, ⟨.or, [17, 14]⟩, ⟨.and, [28, 22]⟩, ⟨.and, [24, 26]⟩, ⟨.or, [32, 29]⟩, ⟨.or, [7, 33]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [30, 2]⟩, ⟨.and, [19, 20]⟩, ⟨.or, [23, 27]⟩, ⟨.and, [38, 34]⟩, ⟨.and, [36, 35]⟩, ⟨.or, [40, 39]⟩, ⟨.or, [37, 31]⟩, ⟨.or, [41, 42]⟩], 43⟩

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

end PEqualNP.Outside.L_meta_19719_aux

open PEqualNP.Outside.L_meta_19719_aux in
theorem PEqualNP.Outside.L_meta_19719 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
