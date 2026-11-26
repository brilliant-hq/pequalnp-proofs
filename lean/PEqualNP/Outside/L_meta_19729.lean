import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19729_aux

def witness : Circuit :=
  ⟨[⟨.or, [2, 5]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [2, 17]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [13, 6]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [18, 10]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [20, 21]⟩, ⟨.or, [19, 18]⟩, ⟨.and, [27, 23]⟩, ⟨.or, [20, 0]⟩, ⟨.or, [22, 21]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [24, 1]⟩, ⟨.and, [25, 29]⟩, ⟨.or, [31, 1]⟩, ⟨.or, [17, 30]⟩, ⟨.and, [34, 26]⟩, ⟨.and, [35, 32]⟩, ⟨.or, [33, 37]⟩, ⟨.or, [38, 28]⟩, ⟨.or, [36, 39]⟩], 40⟩

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

end PEqualNP.Outside.L_meta_19729_aux

open PEqualNP.Outside.L_meta_19729_aux in
theorem PEqualNP.Outside.L_meta_19729 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9589595487171930210 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
