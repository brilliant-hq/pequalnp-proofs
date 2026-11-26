import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19717_aux

def witness : Circuit :=
  ⟨[⟨.or, [3, 13]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [17, 18]⟩, ⟨.or, [15, 8]⟩, ⟨.or, [13, 9]⟩, ⟨.or, [18, 2]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [21, 20]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [16, 11]⟩, ⟨.or, [15, 25]⟩, ⟨.or, [4, 24]⟩, ⟨.or, [23, 28]⟩, ⟨.and, [26, 6]⟩, ⟨.or, [30, 20]⟩, ⟨.and, [33, 31]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [35, 4]⟩, ⟨.and, [35, 29]⟩, ⟨.or, [18, 36]⟩, ⟨.or, [28, 38]⟩, ⟨.and, [39, 27]⟩, ⟨.or, [40, 34]⟩, ⟨.or, [37, 19]⟩, ⟨.or, [32, 42]⟩, ⟨.or, [41, 43]⟩], 44⟩

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

end PEqualNP.Outside.L_meta_19717_aux

open PEqualNP.Outside.L_meta_19717_aux in
theorem PEqualNP.Outside.L_meta_19717 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
