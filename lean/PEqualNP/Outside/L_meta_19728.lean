import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19728_aux

def witness : Circuit :=
  ⟨[⟨.or, [5, 15]⟩, ⟨.or, [10, 0]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [14, 3]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [4, 20]⟩, ⟨.or, [7, 17]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [7, 19]⟩, ⟨.or, [6, 19]⟩, ⟨.or, [8, 21]⟩, ⟨.or, [7, 26]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [18, 25]⟩, ⟨.or, [30, 21]⟩, ⟨.or, [2, 16]⟩, ⟨.and, [24, 23]⟩, ⟨.and, [22, 31]⟩, ⟨.or, [6, 33]⟩, ⟨.or, [23, 24]⟩, ⟨.or, [26, 8]⟩, ⟨.or, [2, 18]⟩, ⟨.or, [29, 37]⟩, ⟨.and, [39, 38]⟩, ⟨.and, [27, 28]⟩, ⟨.or, [41, 40]⟩, ⟨.or, [32, 35]⟩, ⟨.or, [34, 42]⟩, ⟨.and, [36, 43]⟩, ⟨.or, [45, 44]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_19728_aux

open PEqualNP.Outside.L_meta_19728_aux in
theorem PEqualNP.Outside.L_meta_19728 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
