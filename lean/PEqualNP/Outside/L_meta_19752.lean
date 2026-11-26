import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19752_aux

def witness : Circuit :=
  ⟨[⟨.or, [3, 9]⟩, ⟨.or, [14, 6]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [0, 16]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [2, 20]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [21, 17]⟩, ⟨.and, [23, 18]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [5, 8]⟩, ⟨.and, [12, 6]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [4, 26]⟩, ⟨.and, [22, 29]⟩, ⟨.or, [2, 25]⟩, ⟨.or, [26, 21]⟩, ⟨.and, [15, 31]⟩, ⟨.and, [19, 32]⟩, ⟨.or, [30, 33]⟩, ⟨.or, [24, 34]⟩, ⟨.or, [28, 0]⟩, ⟨.and, [13, 37]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [27, 39]⟩, ⟨.or, [38, 40]⟩], 41⟩

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

end PEqualNP.Outside.L_meta_19752_aux

open PEqualNP.Outside.L_meta_19752_aux in
theorem PEqualNP.Outside.L_meta_19752 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
