import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19755_aux

def witness : Circuit :=
  ⟨[⟨.or, [7, 9]⟩, ⟨.or, [13, 0]⟩, ⟨.or, [5, 15]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [21, 18]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [14, 2]⟩, ⟨.or, [23, 24]⟩, ⟨.or, [10, 19]⟩, ⟨.or, [24, 20]⟩, ⟨.or, [16, 22]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [21, 10]⟩, ⟨.or, [17, 23]⟩, ⟨.or, [29, 20]⟩, ⟨.and, [27, 28]⟩, ⟨.and, [32, 25]⟩, ⟨.or, [26, 18]⟩, ⟨.or, [3, 22]⟩, ⟨.or, [36, 30]⟩, ⟨.and, [30, 19]⟩, ⟨.or, [16, 38]⟩, ⟨.and, [39, 37]⟩, ⟨.and, [31, 35]⟩, ⟨.or, [40, 34]⟩, ⟨.or, [41, 42]⟩, ⟨.or, [33, 43]⟩, ⟨.and, [12, 1]⟩, ⟨.or, [45, 44]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_19755_aux

open PEqualNP.Outside.L_meta_19755_aux in
theorem PEqualNP.Outside.L_meta_19755 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
