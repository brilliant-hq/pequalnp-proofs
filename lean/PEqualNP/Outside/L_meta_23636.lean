import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23636_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [7, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [15, 17]⟩, ⟨.and, [14, 18]⟩, ⟨.or, [13, 19]⟩], 20⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : Monotone2 witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_23636_aux

theorem PEqualNP.Outside.L_meta_23636 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275254 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨PEqualNP.Outside.L_meta_23636_aux.witness, PEqualNP.Outside.L_meta_23636_aux.witnessFit, by decide, by decide +kernel⟩
