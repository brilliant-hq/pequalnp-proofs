import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19552_aux

def witness : Circuit :=
  ⟨[⟨.or, [4, 9]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [15, 5]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [19, 10]⟩, ⟨.or, [14, 2]⟩, ⟨.or, [23, 18]⟩, ⟨.or, [19, 23]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [3, 20]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [28, 10]⟩, ⟨.or, [26, 11]⟩, ⟨.or, [16, 28]⟩, ⟨.or, [20, 21]⟩, ⟨.and, [32, 25]⟩, ⟨.and, [3, 21]⟩, ⟨.and, [29, 27]⟩, ⟨.or, [22, 26]⟩, ⟨.and, [31, 36]⟩, ⟨.and, [30, 24]⟩, ⟨.or, [35, 33]⟩, ⟨.or, [38, 37]⟩, ⟨.or, [34, 40]⟩, ⟨.or, [41, 39]⟩], 42⟩

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

end PEqualNP.Outside.L_meta_19552_aux

open PEqualNP.Outside.L_meta_19552_aux in
theorem PEqualNP.Outside.L_meta_19552 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
