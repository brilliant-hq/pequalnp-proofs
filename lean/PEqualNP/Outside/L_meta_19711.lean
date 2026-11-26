import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19711_aux

def witness : Circuit :=
  ⟨[⟨.or, [6, 0]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [18, 11]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [12, 3]⟩, ⟨.or, [15, 2]⟩, ⟨.and, [16, 13]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [4, 18]⟩, ⟨.or, [21, 0]⟩, ⟨.or, [6, 24]⟩, ⟨.or, [18, 13]⟩, ⟨.or, [25, 22]⟩, ⟨.or, [26, 28]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [4, 16]⟩, ⟨.or, [5, 15]⟩, ⟨.or, [29, 8]⟩, ⟨.and, [31, 32]⟩, ⟨.or, [21, 11]⟩, ⟨.or, [17, 2]⟩, ⟨.and, [33, 27]⟩, ⟨.and, [30, 37]⟩, ⟨.and, [34, 36]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [42, 35]⟩, ⟨.or, [43, 23]⟩], 44⟩

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

end PEqualNP.Outside.L_meta_19711_aux

open PEqualNP.Outside.L_meta_19711_aux in
theorem PEqualNP.Outside.L_meta_19711 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
